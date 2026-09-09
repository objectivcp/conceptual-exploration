import time

from core.context import PartialContext
from experts.base import Expert
from exploration.attribute import AttributeExploration
from exploration.base import ExplorationBase


class SimulatedExpert(Expert[str, str]):
    def __init__(self, context: PartialContext[str, str]):
        self.context = context

    def validate(self, implication, attributes=None):
        for o in self.context.objects.values():
            if o.refutes(implication):
                return o
        return None

expert_context = PartialContext.from_cxt('test.cxt')
base = ExplorationBase(attributes=expert_context.attributes)
exploration = AttributeExploration(base, SimulatedExpert(expert_context))

start = time.perf_counter()
exploration.run()
elapsed = time.perf_counter() - start
print(f"exploration.run() took {elapsed:.6f} seconds")
print(f'and produced {len(base.implications.implications)} implications.')
