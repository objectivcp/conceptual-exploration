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

    # The unconfirmed implication whose refutation stopped the exploration,
    # if one did.
    stopped_by: object = None