# TLA+ Code Instructions

## Examples

![ARAT](/img/TLA-ARAT.png)

![NRAT](/img/TLA-NRAT.png)

![NRNT](/img/TLA-NRNT.png)

## How to run

- Install and open ![TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1#latest-tla-files)
- Goto `File > Open Spec > Add New Spec` and select one from `MSI_ARAT.tla, MSI_NRAT.tla, MSI_NRNT.tla`
- Goto `TLC Model Checker > New Model...` 
- In the Model Overview `What to check? / Invariants` section, add a formula `Invariants`
- In the `What is the model?` section, specify the max writes and number of cores (We used `MaxWrite <- 5, CoreNum <- 4`, for quicker result you can run a smaller model)
- (Optional) For quicker result, click `What to check? / Additional TLC Options`, goto `Features` and turn off profiling
- Run the model
- (Optional) In `MSI_ARAT.tla`, change `Spec == Init /\ [][Next /\ atomicRequest]_vars` to `Spec == Init /\ [][Next /\ atomicTransaction]_vars` or `Spec == Init /\ [][Next]_vars` and run again, see why it doesn't work under non-atomic buses.
