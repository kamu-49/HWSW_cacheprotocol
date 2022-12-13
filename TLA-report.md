# TLA Report (In Progress)

## Contributions
- Try model MSI with PlusCal
- Model check 3 MSI modules that evolve from atomic request/transaction to non-atomic with TLA+, which ranged from 6 to 14 states for the cache controllers and 4 states for the memory controller.


## Observations
- Can't check `[]AtomicRequest => []Coherence` property because of deadlock
- Painful to extend a module:
  - When adding a variable I have change all the `UNCHANGED`
  - Lack of polymorphism

