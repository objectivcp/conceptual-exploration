from dataclasses import dataclass
from dataclasses import field


@dataclass
class ExplorationState:

    questions_asked: int = 0

    accepted_implications: list = field(
        default_factory=list
    )

    counterexamples: list = field(
        default_factory=list
    )