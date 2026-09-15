from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Paths:
    root: Path
    bin_dir: Path
    scripts_dir: Path
    src_dir: Path
    workspace_dir: Path
    prompts_dir: Path
    contexts_dir: Path
    lean_project_dir: Path
    data_dir: Path
    runs_dir: Path
    logs_dir: Path


def default_paths() -> Paths:
    root = Path(__file__).resolve().parents[2]
    workspace_dir = root / "workspace"
    return Paths(
        root=root,
        bin_dir=root / "bin",
        scripts_dir=root / "scripts",
        src_dir=root / "src",
        workspace_dir=workspace_dir,
        prompts_dir=workspace_dir / "prompts",
        contexts_dir=workspace_dir / "contexts",
        lean_project_dir=workspace_dir / "lean_project",
        data_dir=root / "data",
        runs_dir=root / "data" / "runs",
        logs_dir=root / "logs",
    )


def ensure_layout(paths: Paths) -> None:
    for directory in (
        paths.bin_dir,
        paths.scripts_dir,
        paths.src_dir,
        paths.workspace_dir,
        paths.prompts_dir,
        paths.contexts_dir,
        paths.lean_project_dir,
        paths.data_dir,
        paths.runs_dir,
        paths.logs_dir,
    ):
        directory.mkdir(parents=True, exist_ok=True)
