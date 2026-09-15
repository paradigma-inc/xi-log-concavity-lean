import shutil
from datetime import datetime, timezone
from pathlib import Path

import typer
from rich import print as rprint

from tproof.constants import (
    LEAN_TOOLCHAIN,
    MATHLIB_HASH,
    OPS_AGENT_NOTES,
    OPS_AGENT_ROLE,
    PACKAGE_NAME,
    PROOF_AGENT_NOTES,
    PROOF_AGENT_ROLE,
)
from tproof.layout import Paths, default_paths, ensure_layout
from tproof.leanops import (
    ensure_toolchain_installed,
    lake_build,
    lake_update,
    reindex_allproofs,
    seed_lean_project,
    snapshot_project,
)
from tproof.runstore import create_run, load_run, new_run_id, now_utc_iso, save_run
from tproof.tasking import (
    build_run_brief,
    discover_project_modules,
    find_sorry_hits,
    read_task_prompt,
)

app = typer.Typer(no_args_is_help=True, help="Local Lean theorem proving pipeline CLI")


def _paths() -> Paths:
    paths = default_paths()
    ensure_layout(paths)
    return paths


def _write_log(log_path: Path, text: str) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")


def _find_forbidden_staging_artifacts(paths: Paths) -> list[str]:
    staging_dir = paths.workspace_dir / "staging"
    if not staging_dir.is_dir():
        return []
    blocked_suffixes = {".lean", ".md"}
    hits: list[str] = []
    for file_path in sorted(staging_dir.rglob("*")):
        if not file_path.is_file():
            continue
        if file_path.name == ".gitkeep":
            continue
        if file_path.suffix.lower() in blocked_suffixes:
            hits.append(str(file_path.relative_to(paths.root)))
    return hits


def _which(binary: str) -> str | None:
    return shutil.which(binary)


@app.command("doctor")
def doctor() -> None:
    paths = _paths()
    lean_path = _which("lean")
    lake_path = _which("lake")
    elan_path = _which("elan")

    if not lean_path or not lake_path or not elan_path:
        raise RuntimeError(
            "Missing required binaries. Ensure `lean`, `lake`, and `elan` are installed and on PATH."
        )

    from tproof.leanops import run_cmd

    lean_code, lean_out = run_cmd(["lean", "--version"], cwd=paths.root)
    lake_code, lake_out = run_cmd(["lake", "--version"], cwd=paths.root)
    if lean_code != 0 or lake_code != 0:
        raise RuntimeError("Unable to run `lean --version` or `lake --version`.")

    rprint(f"[green]lean:[/green] {lean_path}")
    rprint(f"[green]lake:[/green] {lake_path}")
    rprint(f"[green]elan:[/green] {elan_path}")
    rprint(f"[green]Pinned toolchain:[/green] {LEAN_TOOLCHAIN}")
    rprint(f"[green]Pinned mathlib hash:[/green] {MATHLIB_HASH}")
    rprint(f"[green]Proof worker:[/green] {PROOF_AGENT_ROLE}")
    rprint(f"[green]Proof notes:[/green] {PROOF_AGENT_NOTES}")
    rprint(f"[green]Ops worker:[/green] {OPS_AGENT_ROLE}")
    rprint(f"[green]Ops notes:[/green] {OPS_AGENT_NOTES}")
    rprint(f"[green]Lean project path:[/green] {paths.lean_project_dir}")
    rprint(lean_out.strip())
    rprint(lake_out.strip())


@app.command("init")
def init(build: bool = typer.Option(True, "--build/--no-build")) -> None:
    paths = _paths()
    seed_lean_project(
        paths.lean_project_dir,
        lean_toolchain=LEAN_TOOLCHAIN,
        mathlib_hash=MATHLIB_HASH,
    )
    reindex_allproofs(paths.lean_project_dir)

    install_code, install_out = ensure_toolchain_installed(LEAN_TOOLCHAIN)
    already_installed = "already installed" in install_out.lower()
    if install_code != 0 and not already_installed:
        raise RuntimeError(f"elan toolchain install failed:\n{install_out}")

    update_code, update_out = lake_update(paths.lean_project_dir)
    if update_code != 0:
        raise RuntimeError(f"lake update failed:\n{update_out}")

    logs = [
        "== elan toolchain install ==",
        install_out,
        "== lake update ==",
        update_out,
    ]
    if build:
        build_code, build_out = lake_build(paths.lean_project_dir)
        if build_code != 0:
            raise RuntimeError(f"lake build failed:\n{build_out}")
        logs.extend(["== lake build ==", build_out])

    log_name = datetime.now(timezone.utc).strftime("init_%Y%m%dT%H%M%SZ.log")
    _write_log(paths.logs_dir / log_name, "\n".join(logs))
    rprint(f"[green]Workspace initialized:[/green] {paths.lean_project_dir}")
    rprint(f"[green]Toolchain:[/green] {LEAN_TOOLCHAIN}")
    rprint(f"[green]Mathlib hash:[/green] {MATHLIB_HASH}")


@app.command("reindex")
def reindex(project_dir: Path | None = typer.Option(None, "--project-dir")) -> None:
    paths = _paths()
    target = project_dir or paths.lean_project_dir
    all_proofs_path = reindex_allproofs(target)
    rprint(f"[green]Reindexed:[/green] {all_proofs_path}")


@app.command("start-run")
def start_run(
    prompt_file: Path | None = typer.Option(None, "--prompt-file"),
    prompt_text: str | None = typer.Option(None, "--prompt-text"),
    run_label: str | None = typer.Option(None, "--run-label"),
    context_file: Path | None = typer.Option(None, "--context-file"),
) -> None:
    paths = _paths()
    task_prompt = read_task_prompt(prompt_file=prompt_file, prompt_text=prompt_text)
    context_text = context_file.read_text(encoding="utf-8") if context_file else None
    modules = discover_project_modules(paths.lean_project_dir)
    sorry_hits = find_sorry_hits(paths.lean_project_dir)

    run_id = new_run_id(run_label)
    run = {
        "run_id": run_id,
        "created_at": now_utc_iso(),
        "updated_at": now_utc_iso(),
        "status": "READY_FOR_PROOF",
        "task_prompt": task_prompt,
        "context_file": str(context_file.resolve()) if context_file else None,
        "context_text": context_text,
        "known_modules": modules,
        "sorry_hits": sorry_hits,
        "proof_agent_role": PROOF_AGENT_ROLE,
        "proof_agent_notes": PROOF_AGENT_NOTES,
        "ops_agent_role": OPS_AGENT_ROLE,
        "ops_agent_notes": OPS_AGENT_NOTES,
        "lean_project_dir": str(paths.lean_project_dir),
    }
    create_run(paths, run_id, run)

    run_dir = paths.runs_dir / run_id
    snapshot_project(paths.lean_project_dir, run_dir / "project_snapshot")
    (run_dir / "task_prompt.txt").write_text(task_prompt, encoding="utf-8")
    if context_text:
        (run_dir / "context.txt").write_text(context_text, encoding="utf-8")
    brief = build_run_brief(
        run_id=run_id,
        task_prompt=task_prompt,
        known_modules=modules,
        sorry_hits=sorry_hits,
        context_text=context_text,
    )
    (run_dir / "run_brief.md").write_text(brief, encoding="utf-8")

    rprint(f"[green]Run created:[/green] {run_id}")
    rprint(f"[green]Run file:[/green] {run_dir / 'run.json'}")
    rprint(f"[green]Brief file:[/green] {run_dir / 'run_brief.md'}")
    rprint(f"[green]Outstanding sorries:[/green] {len(sorry_hits)}")


@app.command("show-run")
def show_run(run_id: str = typer.Argument(...)) -> None:
    paths = _paths()
    run = load_run(paths, run_id)
    rprint(run)


@app.command("set-status")
def set_status(
    run_id: str = typer.Argument(...),
    status: str = typer.Argument(...),
    note: str | None = typer.Option(None, "--note"),
) -> None:
    paths = _paths()
    run = load_run(paths, run_id)
    run["status"] = status
    run["updated_at"] = now_utc_iso()
    if note:
        run["note"] = note
    save_run(paths, run_id, run)
    rprint(f"[green]Updated run {run_id} -> {status}[/green]")


@app.command("verify")
def verify(project_dir: Path | None = typer.Option(None, "--project-dir")) -> None:
    paths = _paths()
    target = project_dir or paths.lean_project_dir
    code, output = lake_build(target)
    sorry_hits = find_sorry_hits(target)
    forbidden_staging_hits = _find_forbidden_staging_artifacts(paths)
    log_name = datetime.now(timezone.utc).strftime("verify_%Y%m%dT%H%M%SZ.log")
    log_path = paths.logs_dir / log_name
    extra = ""
    if sorry_hits:
        extra = "\n\n== unresolved sorry locations ==\n" + "\n".join(sorry_hits)
    if forbidden_staging_hits:
        extra += "\n\n== forbidden artifacts under workspace/staging ==\n" + "\n".join(
            forbidden_staging_hits
        )
    _write_log(log_path, output + extra)

    if code != 0 or sorry_hits or forbidden_staging_hits:
        rprint(f"[red]Verification failed.[/red] Log: {log_path}")
        if sorry_hits:
            rprint(f"[red]Unresolved sorries:[/red] {len(sorry_hits)}")
        if forbidden_staging_hits:
            rprint(
                "[red]Forbidden staging artifacts:[/red] "
                f"{len(forbidden_staging_hits)} (move them to ProofWorkspace/Final)"
            )
        raise typer.Exit(code=1)
    rprint(f"[green]Verification passed.[/green] Log: {log_path}")


@app.command("smoke-test")
def smoke_test() -> None:
    paths = _paths()
    init(build=True)

    smoke_dir = paths.lean_project_dir / PACKAGE_NAME / "Smoke"
    smoke_dir.mkdir(parents=True, exist_ok=True)
    smoke_file = smoke_dir / "Smoke.lean"
    smoke_file.write_text(
        """import Mathlib

namespace ProofWorkspace.Smoke

theorem smoke_add_comm (a b : Nat) : a + b = b + a := by
  sorry

end ProofWorkspace.Smoke
""",
        encoding="utf-8",
    )
    reindex_allproofs(paths.lean_project_dir)

    run_id_label = "smoke"
    start_run(
        prompt_text="Fill all sorry placeholders while preserving theorem statements.",
        run_label=run_id_label,
        prompt_file=None,
        context_file=None,
    )

    try:
        verify(project_dir=paths.lean_project_dir)
    except typer.Exit:
        rprint("[green]Smoke test passed:[/green] pipeline detects unresolved `sorry` correctly.")
        return
    raise RuntimeError(
        "Smoke test expected verification failure before proving, but verify passed."
    )


def main() -> None:
    app()


if __name__ == "__main__":
    main()
