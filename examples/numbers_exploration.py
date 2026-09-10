import random
from typing import TypeVar, Generic

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from typing import Callable

from conceptual_exploration.exploration.attribute import AttributeExploration
from conceptual_exploration.exploration.base import ExplorationBase

O = TypeVar("O")


class NamedPredicate(Generic[O]):
    def __init__(self, name: str, predicate: Callable[[O], bool]):
        self.name = name
        self.predicate = predicate

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def __call__(self, o: O) -> bool:
        return self.predicate(o)

    def __lt__(self, other: "NamedPredicate[O]") -> bool:
        return self.name < other.name


class NumberExpert(Expert[int, NamedPredicate[int]]):
    def __init__(self, max_integer: int, predicates: list[NamedPredicate[int]]):
        self.max = max_integer
        self.predicates = predicates
        
    def validate(self, impl, attributes=None):
        print(f'Validating {impl}')

        for i in range(1, self.max + 1):

            if all(a(i) for a in impl.premise) and any(not a(i) for a in impl.conclusion):

                valid_predicates = set(p for p in self.predicates if p(i))

                positive = set(impl.premise)
                positive.update(
                    p
                    for p in valid_predicates - positive
                    if random.choice([True, False])
                )

                negative = {random.choice(tuple(impl.conclusion - valid_predicates))}
                negative.update(
                    p
                    for p in set(self.predicates) - valid_predicates - negative
                    if random.choice([True, False])
                )

                return PartialObject(i, positive, negative)

        return None
    

def is_prime(n):
    if n == 1:
        return False

    for m in range(2, n//2 + 1):
        if n % m == 0:
            return False

    return True


def is_factorial(n):
    f = 1
    for m in range(2, n + 1):
        f *= m
        if f >= n:
            break
    return f == n


attributes = [
    NamedPredicate("even", lambda n: n % 2 == 0),
    NamedPredicate("odd", lambda n: n % 2 == 1),
    NamedPredicate("divisible_by_three", lambda n: n % 3 == 0),
    NamedPredicate("prime", is_prime),
    NamedPredicate("factorial", is_factorial),
]

base = ExplorationBase(attributes=attributes)
exploration = AttributeExploration(base, NumberExpert(100, attributes))
exploration.run()

print()
for implication in base.implications:
    print(implication)
print()
print(base.context)