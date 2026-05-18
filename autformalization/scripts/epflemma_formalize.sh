#!/bin/bash

epflemma project init
epflemma workflow --provider codex formalize docs/
epflemma workflow --provider codex prove --additional-skill .epflemma/skills/formalization-blueprint-ShadowBench-Source-Main/SKILL.md
# epflemma workflow prove --additional-skill .epflemma/skills/formalization-blueprint-ShadowBench-Source-Main/SKILL.md