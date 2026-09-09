from collections.abc import Generator
from typing import Generic, TypeVar

A = TypeVar("A")


class NextClosure(Generic[A]):

    def __init__(self, attributes, closure_operator):
        self.attributes = tuple(attributes)
        self.closure_operator = closure_operator
        self.prefixes = [
            frozenset(self.attributes[:k]) for k in range(len(self.attributes) + 1)
        ]

    def generate(self) -> Generator[frozenset[A], bool | None, None]:

        s = self.closure_operator(frozenset())
        if (yield frozenset(s)):  # closure of s changed by caller
            s = self.closure_operator(s)

        i = len(self.attributes)
        while i > 0:
            i -= 1
            a = self.attributes[i]
            if a in s:
                s.remove(a)
            else:
                t = self.closure_operator(s | {a})
                if (t - s).isdisjoint(self.prefixes[i]):
                    if (yield frozenset(t)):
                        t_closed = self.closure_operator(t)
                        if (t_closed - t).isdisjoint(self.prefixes[i]):
                            s = t_closed
                            i = len(self.attributes)
                    else:
                        s = t
                        i = len(self.attributes)
