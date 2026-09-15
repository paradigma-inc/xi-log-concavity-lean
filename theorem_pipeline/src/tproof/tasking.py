import re
from pathlib import Path

from tproof.constants import (
    OPS_AGENT_NOTES,
    OPS_AGENT_ROLE,
    PACKAGE_NAME,
    PROOF_AGENT_NOTES,
    PROOF_AGENT_ROLE,
)


def read_task_prompt(prompt_file: Path | None, prompt_text: str | None) -> str:
    if prompt_file and prompt_text:
        raise ValueError("Pass either --prompt-file or --prompt-text, not both.")
    if prompt_file:
        return prompt_file.read_text(encoding="utf-8").strip()
    if prompt_text:
        return prompt_text.strip()
    raise ValueError("Pass one of --prompt-file or --prompt-text.")


def discover_project_modules(project_dir: Path) -> list[str]:
    package_dir = project_dir / PACKAGE_NAME
    if not package_dir.is_dir():
        return []

    modules: list[str] = []
    for lean_file in sorted(package_dir.rglob("*.lean")):
        rel = lean_file.relative_to(project_dir).with_suffix("")
        module_name = ".".join(rel.parts)
        if module_name.endswith(".AllProofs"):
            continue
        modules.append(module_name)
    return modules


def find_sorry_hits(project_dir: Path) -> list[str]:
    word = re.compile(r"\bsorry\b")
    hits: list[str] = []
    package_dir = project_dir / PACKAGE_NAME
    if not package_dir.is_dir():
        return hits

    for lean_file in sorted(package_dir.rglob("*.lean")):
        rel = lean_file.relative_to(project_dir)
        lines = lean_file.read_text(encoding="utf-8").splitlines()
        for line_number, line in enumerate(lines, start=1):
            if word.search(line):
                hits.append(f"{rel}:{line_number}")
    return hits


def build_run_brief(
    *,
    run_id: str,
    task_prompt: str,
    known_modules: list[str],
    sorry_hits: list[str],
    context_text: str | None,
) -> str:
    module_block = "\n".join(f"- {module}" for module in known_modules) or "- (none)"
    sorry_block = "\n".join(f"- {hit}" for hit in sorry_hits) or "- (none)"
    context_block = context_text.strip() if context_text else "(none)"

    return f"""# Run Brief: {run_id}

## Task
{task_prompt}

## Context
{context_block}

## Known Modules
{module_block}

## Outstanding `sorry` Locations
{sorry_block}

## Model Routing (Required)
1. Mathematical proving worker:
   - Profile: `{PROOF_AGENT_ROLE}`
   - Guidance: {PROOF_AGENT_NOTES}
   - Scope: theorem proving, proof search, lemma decomposition, difficult Lean terms.
2. Programming/ops/reporting worker:
   - Profile: `{OPS_AGENT_ROLE}`
   - Guidance: {OPS_AGENT_NOTES}
   - Scope: scripts, repo hygiene, status summaries, verification logs, run metadata updates.

## Execution Pattern
1. Ask the proving worker to edit files under `workspace/lean_project/`.
2. Ask the ops worker to run `uv run -m tproof.cli verify` and summarize failures.
3. Iterate until verification passes with no `sorry`.
"""
