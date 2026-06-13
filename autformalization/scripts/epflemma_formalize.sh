#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PROBLEM_DIR=""
PHASE="both"
PROVIDER="codex"
PROJECT_INIT="auto"
LAKE_UPDATE=0
CHECK_BEFORE=0
CHECK_AFTER=0
PROOF_GUARD="auto"
PROOF_GUARD_REQUIRE_ALLOWED_IMPORTS=0
SHADOWBENCH_SKILL="$ROOT/skills/shadowbench-formalization-context/SKILL.md"
PROOF_GUARD_SCRIPT="$SCRIPT_DIR/shadowbench_proof_guard.py"
PROOF_GUARD_SNAPSHOT=".epflemma/proof-guard-before.json"

usage() {
  cat <<'USAGE'
Usage:
  epflemma_formalize.sh [options]

Run EPFLemma on one ShadowBench problem project.

Options:
  --problem IDX_OR_DIR       Problem id such as algebra/L2/alg_comp_L2_001, or a directory.
  --problem-dir DIR          Explicit problem project directory.
  --phase PHASE              init, formalize, prove, both, or check. Default: both.
  --provider PROVIDER        EPFLemma provider. Default: codex.
  --lake-update              Run lake update before EPFLemma.
  --check-before             Run lake env lean before EPFLemma.
  --check-after              Run lake env lean after EPFLemma.
  --proof-guard              Reject prove runs that change imports or required declaration statements.
  --no-proof-guard           Disable the prove-only import/statement guard.
  --proof-guard-require-allowed-imports
                              Also require current imports to match docs/instructions.md.
  --force-project-init       Run epflemma project init even if .epflemma/project.yaml exists.
  --no-project-init          Skip epflemma project init for workflow phases.
  -h, --help                 Show this help.

If no problem is provided, the current directory must be a problem project.
USAGE
}

die() {
  echo "error: $*" >&2
  exit 2
}

resolve_problem() {
  local value="$1"
  local candidate=""
  if [[ -z "$value" ]]; then
    if [[ -f "ShadowBench/Source/Main.lean" && -f "docs/source.tex" ]]; then
      pwd
      return
    fi
    die "no problem selected and current directory is not a ShadowBench problem project"
  fi

  for candidate in \
    "$value" \
    "$ROOT/$value" \
    "$ROOT/problems/$value"
  do
    if [[ -d "$candidate" && -f "$candidate/ShadowBench/Source/Main.lean" ]]; then
      cd "$candidate" && pwd
      return
    fi
  done

  local basename_match
  basename_match="$(find "$ROOT/problems" -mindepth 3 -maxdepth 3 -type d -name "$(basename "$value")" | sort | head -n 1 || true)"
  if [[ -n "$basename_match" && -f "$basename_match/ShadowBench/Source/Main.lean" ]]; then
    cd "$basename_match" && pwd
    return
  fi

  die "could not resolve problem: $value"
}

run_cmd() {
  printf '+'
  printf ' %q' "$@"
  printf '\n'
  "$@"
}

run_cmd_no_stdin() {
  printf '+'
  printf ' %q' "$@"
  printf ' </dev/null\n'
  "$@" </dev/null
}

run_cmd_with_exit_command() {
  printf "+ printf '/exit\\n' |"
  printf ' %q' "$@"
  printf '\n'
  printf '/exit\n' | "$@"
}

proof_guard_enabled() {
  case "$PROOF_GUARD" in
    always)
      return 0
      ;;
    never)
      return 1
      ;;
    auto)
      [[ "$PHASE" == "prove" ]]
      ;;
    *)
      die "internal error: unknown proof guard mode: $PROOF_GUARD"
      ;;
  esac
}

proof_guard_args() {
  if [[ "$PROOF_GUARD_REQUIRE_ALLOWED_IMPORTS" -eq 1 ]]; then
    printf '%s\n' --require-allowed-imports
  fi
}

proof_guard_snapshot() {
  mapfile -t GUARD_ARGS < <(proof_guard_args)
  run_cmd python3 "$PROOF_GUARD_SCRIPT" snapshot --problem-dir "$PROBLEM_DIR" --output "$PROOF_GUARD_SNAPSHOT" "${GUARD_ARGS[@]}"
}

proof_guard_check() {
  mapfile -t GUARD_ARGS < <(proof_guard_args)
  run_cmd python3 "$PROOF_GUARD_SCRIPT" check --problem-dir "$PROBLEM_DIR" --input "$PROOF_GUARD_SNAPSHOT" "${GUARD_ARGS[@]}"
}

run_project_init() {
  case "$PROJECT_INIT" in
    always)
      run_cmd_no_stdin epflemma project init
      ;;
    auto)
      if [[ -f ".epflemma/project.yaml" ]]; then
        echo "+ epflemma project init (skipped: .epflemma/project.yaml exists)"
      else
        run_cmd_no_stdin epflemma project init
      fi
      ;;
    never)
      ;;
    *)
      die "internal error: unknown project init mode: $PROJECT_INIT"
      ;;
  esac
}

shadowbench_skill_args() {
  if [[ -f "$SHADOWBENCH_SKILL" ]]; then
    printf '%s\n' --additional-skill "$SHADOWBENCH_SKILL"
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --problem)
      [[ $# -ge 2 ]] || die "--problem requires a value"
      PROBLEM_DIR="$(resolve_problem "$2")"
      shift 2
      ;;
    --problem-dir)
      [[ $# -ge 2 ]] || die "--problem-dir requires a value"
      PROBLEM_DIR="$(resolve_problem "$2")"
      shift 2
      ;;
    --phase)
      [[ $# -ge 2 ]] || die "--phase requires a value"
      PHASE="$2"
      shift 2
      ;;
    --provider)
      [[ $# -ge 2 ]] || die "--provider requires a value"
      PROVIDER="$2"
      shift 2
      ;;
    --lake-update)
      LAKE_UPDATE=1
      shift
      ;;
    --check-before)
      CHECK_BEFORE=1
      shift
      ;;
    --check-after)
      CHECK_AFTER=1
      shift
      ;;
    --proof-guard)
      PROOF_GUARD="always"
      shift
      ;;
    --no-proof-guard)
      PROOF_GUARD="never"
      shift
      ;;
    --proof-guard-require-allowed-imports)
      PROOF_GUARD_REQUIRE_ALLOWED_IMPORTS=1
      shift
      ;;
    --no-project-init)
      PROJECT_INIT="never"
      shift
      ;;
    --force-project-init)
      PROJECT_INIT="always"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown argument: $1"
      ;;
  esac
done

case "$PHASE" in
  init|formalize|prove|both|check) ;;
  *) die "--phase must be one of: init, formalize, prove, both, check" ;;
esac

if [[ -z "$PROBLEM_DIR" ]]; then
  PROBLEM_DIR="$(resolve_problem "")"
fi

cd "$PROBLEM_DIR"
echo "Problem directory: $PROBLEM_DIR"

if [[ "$LAKE_UPDATE" -eq 1 ]]; then
  run_cmd lake update
fi

if [[ "$CHECK_BEFORE" -eq 1 ]]; then
  run_cmd lake env lean ShadowBench/Source/Main.lean
fi

if [[ "$PHASE" == "init" ]]; then
  PROJECT_INIT="always"
  run_project_init
elif [[ "$PHASE" != "check" ]]; then
  run_project_init
fi

if [[ "$PHASE" == "formalize" || "$PHASE" == "both" ]]; then
  mapfile -t FORMALIZE_SKILL_ARGS < <(shadowbench_skill_args)
  run_cmd_with_exit_command epflemma workflow --provider "$PROVIDER" formalize docs/source.tex "${FORMALIZE_SKILL_ARGS[@]}"
fi

if [[ "$PHASE" == "prove" || "$PHASE" == "both" ]]; then
  PROVE_RC=0
  if proof_guard_enabled; then
    proof_guard_snapshot
  fi
  PROVE_ARGS=(workflow --provider "$PROVIDER" prove ShadowBench/Source/Main.lean)
  mapfile -t PROVE_SKILL_ARGS < <(shadowbench_skill_args)
  PROVE_ARGS+=("${PROVE_SKILL_ARGS[@]}")
  BLUEPRINT_SKILL=".epflemma/skills/formalization-blueprint-ShadowBench-Source-Main/SKILL.md"
  if [[ -f "$BLUEPRINT_SKILL" ]]; then
    PROVE_ARGS+=(--additional-skill "$BLUEPRINT_SKILL")
  fi
  run_cmd_with_exit_command epflemma "${PROVE_ARGS[@]}" || PROVE_RC=$?
  if proof_guard_enabled; then
    proof_guard_check
  fi
fi

if [[ "$PHASE" == "check" || "$CHECK_AFTER" -eq 1 ]]; then
  run_cmd lake env lean ShadowBench/Source/Main.lean
fi

if [[ "${PROVE_RC:-0}" -ne 0 ]]; then
  exit "$PROVE_RC"
fi
