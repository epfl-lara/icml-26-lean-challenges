#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PROBLEM_DIR=""
PHASE="both"
PROVIDER="codex"
PROJECT_INIT=1
LAKE_UPDATE=0
CHECK_BEFORE=0
CHECK_AFTER=0
SHADOWBENCH_SKILL="$ROOT/skills/shadowbench-formalization-context/SKILL.md"

usage() {
  cat <<'USAGE'
Usage:
  epflemma_formalize.sh [options]

Run EPFLemma on one ShadowBench problem project.

Options:
  --problem IDX_OR_DIR       Problem id such as algebra/L2/alg_comp_L2_001, or a directory.
  --problem-dir DIR          Explicit problem project directory.
  --phase PHASE              formalize, prove, both, or check. Default: both.
  --provider PROVIDER        EPFLemma provider. Default: codex.
  --lake-update              Run lake update before EPFLemma.
  --check-before             Run lake env lean before EPFLemma.
  --check-after              Run lake env lean after EPFLemma.
  --no-project-init          Skip epflemma project init.
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
    --no-project-init)
      PROJECT_INIT=0
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
  formalize|prove|both|check) ;;
  *) die "--phase must be one of: formalize, prove, both, check" ;;
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

if [[ "$PHASE" != "check" && "$PROJECT_INIT" -eq 1 ]]; then
  run_cmd_no_stdin epflemma project init
fi

if [[ "$PHASE" == "formalize" || "$PHASE" == "both" ]]; then
  mapfile -t FORMALIZE_SKILL_ARGS < <(shadowbench_skill_args)
  run_cmd_no_stdin epflemma workflow --provider "$PROVIDER" formalize docs/source.tex "${FORMALIZE_SKILL_ARGS[@]}"
fi

if [[ "$PHASE" == "prove" || "$PHASE" == "both" ]]; then
  PROVE_ARGS=(workflow --provider "$PROVIDER" prove ShadowBench/Source/Main.lean)
  mapfile -t PROVE_SKILL_ARGS < <(shadowbench_skill_args)
  PROVE_ARGS+=("${PROVE_SKILL_ARGS[@]}")
  BLUEPRINT_SKILL=".epflemma/skills/formalization-blueprint-ShadowBench-Source-Main/SKILL.md"
  if [[ -f "$BLUEPRINT_SKILL" ]]; then
    PROVE_ARGS+=(--additional-skill "$BLUEPRINT_SKILL")
  fi
  run_cmd_no_stdin epflemma "${PROVE_ARGS[@]}"
fi

if [[ "$PHASE" == "check" || "$CHECK_AFTER" -eq 1 ]]; then
  run_cmd lake env lean ShadowBench/Source/Main.lean
fi
