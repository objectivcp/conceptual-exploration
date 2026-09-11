import time

from conceptual_exploration.core.context import PartialContext
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.attribute import AttributeExploration
from conceptual_exploration.exploration.base import ExplorationBase


class SimulatedExpert(Expert[str, str]):
    def __init__(self, context: PartialContext[str, str]):
        self.context = context

    def validate(self, implication, attributes=None):
        for o in self.context.objects.values():
            if o.refutes(implication):
                return o
        return None

from pathlib import Path

expert_cxt_path = Path(__file__).parent / "test.cxt" if (Path(__file__).parent / "test.cxt").exists() else "test.cxt"
expert_context = PartialContext.from_cxt(str(expert_cxt_path))
base = ExplorationBase(attributes=expert_context.attributes)
exploration = AttributeExploration(base, SimulatedExpert(expert_context))

start = time.perf_counter()
exploration.run()
elapsed = time.perf_counter() - start
print(f"exploration.run() took {elapsed:.6f} seconds")
print(f'and produced {len(base.implications.implications)} implications.')
