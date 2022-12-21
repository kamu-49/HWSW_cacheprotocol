# TLA Report

## Introduction to cache protocols

TODO

## Contributions

Our main contribution is model-checking 3 MSI cache protocol variants, which ranged from 6 to 14 states for the cache controllers and 4 states for the memory controller, under different bus assumptions. The difference between those variants is they work in different buses: The simplest one only works on the atomic-request-atomic-transaction bus, while the most complicated one works on the real-world non-atomic bus. What interests us is how the non-atomicity affects the design of the MSI protocol, so we modeled 3 different buses as well, and
- Verified that these variants are correct under corresponding bus atomicity assumptions
- Run the simpler protocols under non-atomic buses, verified that they went wrong, and used the error-tracing feature to see why they didn't work and how the more advanced variants fix the problem.
In the following section, we will talk about which MSI variants we model checked, how we model them along with different buses with TLA+ and our results.

### MSI cache coherence model

Consider one cache line (or other units for atomic data storage/transition) of data under the MSI protocol. For each core in the system, as its name suggested, the data has 3 stable states: "M/Modified" means the data is locally modified and not necessarily synced to the memory, "S/Shared" means that the data is in the read mode and potentially several cores have a copy of this data simultaneously, "I/Invalid" means that data is either not in the local cache or outdated. It's trivial to model the transitions if we only consider the stable states: 
- Before any operation, sync the local cache of other cores to the memory and make sure other cores are not in the M state
- When core A writing data, we set A to the M state and other cores to the I state
- When core A reading data, we set A to the S state

While the idea is straightforward, it's not as easy as it sounds to implement under concurrent circumstances. The way that MSI protocol sync between the cores is bus snooping: every core observe the request sent by other cores on the bus and process them in the same order. An example of a core read timeline would look like this:
1. Core A sends a request on the bus
2. Every core process the request (A included)
3. The memory sends back the requested data
4. Core A receives the data and updates its state

There are 3 kinds of requests that each core can send to the bus:
- GetS: The core wants to read from the memory and become the "S" state
- GetM: The core wants to write to the memory and become the "M" state. It's called "Get" because the core is not in the "M" state now, so it has to fetch the most recent value and make sure other cores have written their changes.
- PutM: The core wants to write to the memory while it's in the "M" state.
There is an Upgrade request we didn't consider because it's optional and doesn't introduce more insight. In our TLA+ program, these are all 3 requests that a core can send to the bus. Moreover, a core can also snoop and process a request on the bus, or write to the local data if permitted, in other words, in the state "M". We model the behavior of the cores in TLA+ as follows:
```
coreAction(core) ==
    \/ coreBusEvent(core) \* snoop and process the request on the bus
    \/ getS(core)
    \/ getM(core)
    \/ putM(core)
    \/ /\ write(core)
       /\ UNCHANGED << state, bus, queue >>
```
The `coreBusEvent(core)` function implements the state transition of the MSI protocol, transient states included.

The memory also has its state machine, but it can't send requests subjectively. All that the memory can do is process the requests on the bus and send/store data accordingly. Combined, we can model the MSI protocol in TLA+ as:
```
Next_MSI = \/ \E core \in Cores: coreAction(core)
           \/ memoryAction
```
So each step of the TLA+ model corresponds to a time slot on the bus where only one core is granted bus access. We choose this abstraction level to model the MSI protocol because we can both show the impact of bus characteristics on the variants of MSI protocols and limit the model complexity.

For a detailed description of the state machine for cores and memory, please refer to [1] and our code.

### Bus model

We are interested in 2 characteristics of the bus: atomic-request, and atomic-transaction. Still, we only consider the requests about the same unit of data. The atomic request means that every request sent by the cores appears on the bus and gets processed immediately, in other words, there won't be any request between a core issuing a request and itself receiving it from the bus. The atomic transaction means that when core A issues a request, other requests will not appear on the bus until A receives the response for the request; However, other cores could issue requests during the transaction. An example of an atomic-transaction but not atomic-request bus could be:
1. Core A issues GetS
2. Core B issues GetS
3. A:GetS appears on the bus and every one process it
4. Memory put data on the bus and A receives the data from the bus
5. B:GetS appears on the bus and every one process it
6. Memory put data on the bus and B receives the data from the bus
Since core B issues a GetS request when the first request from A has not finished, this bus is not atomic-request. However, in step 4 the first transaction for A:GetS finishes, then the request from B appears on the bus in step 5, so it has atomic transaction property.

For simplicity, we call a bus that is atomic-request and atomic-transaction as ARAT bus. Similarly, NRAT means not atomic-request but atomic-transaction, and NRNT means neither atomic-request nor atomic-transaction.

We used a queue to model ARAT and NRAT buses. Whenever a core or the memory sends requests or sends data, a request/data message is added to the global queue. The bus will repeatedly select a message from the queue and broadcast it to everyone. Without other constraints, this model is NRNT because the data returned by the memory could pend in the queue for a long time after the bus chooses other requests to broadcast, so we model the properties in TLA+ as:
```
atomicRequest ==
    /\ Cardinality(queue') <= 1
    /\ isRequest(bus) => (\A msg \in queue': isData(msg))

atomicTransaction ==
    /\ Cardinality({msg \in queue': isData(msg)}) <= 1
    /\ (Cardinality(queue') < Cardinality(queue) /\ isRequest(bus)) => \A msg \in queue': isRequest(msg)
```
where `bus` means the broadcasting message, and `queue` means the pending ones. What the code means is that if
- there is never more than 1 pending message 
- no request can be sent to the queue when there is another request broadcasting
then the bus is ARAT; If
- there is never more than 1 pending data message
- data messages get broadcasted before requests
then the bus is NRAT. A bus that has ARAT/NRAT properties doesn't necessarily satisfy those TLA+ statements, but it's general enough and it creates 3 kinds of buses to model check our MSI variants. Moreover, one can hardly write a single statement equal to the ARAT/NRAT property without getting into trouble, and we'll discuss this issue later.

Our NRNT bus model is different from the model above. In short, we used 2 FIFO queues, one for request and one for data, to model the NRNT bus, because the protocol may deadlock if requests and data share one bus.

### Property and results

The property we want to check is simple: At any time the cache on all cores and the memory are coherent. The results show that all 3 variants of the MSI protocol passed the model checker under corresponding buses, but simpler protocol combined with non-atomic buses will yield counterexamples. The successful results are as follows:

![ARAT](/img/TLA-ARAT.png)

![NRAT](/img/TLA-NRAT.png)

![NRNT](/img/TLA-NRNT.png)


## Observations

### PlusCal

Our first try was to model the protocol with PlusCal, which is a pseudocode-like language that can be translated into TLC+ code. The reason we try PlusCal first is that its syntax is close to programming languages, not math expressions, thus easy to learn and write. However, the expression power of PlusCal is lower than TLC+ and doesn't meet our requirements.

Initially, we modeled each core as a while loop process in PlusCal and used the `with` clause to select a core to run, but the compiler says that the `while` clause can't nest inside a `with` clause. As we must use `with` to select a core and `while` to model the repeating behavior of cores, we have to switch to plain TLA+. With a bit of investigation, we find that the issue is caused by the translation method from PlusCal to TLA+: The translator simulates the PlusCal program nearly on the machine code level with a pc counter. Within the `with` block, the pc counter can't change, but the while loop needs the pc counter to track. Anyway, it turns out that writing state machines with TLC+ is much easier than PlusCal because each transition can be nicely expressed in one statement. 

### Property formatting

It's natural to formulate the properties we want to check as something like `[]AtomicRequest => []Coherence`; However, we found it ending in deadlock in our setups. For example, some state machine transition is unreachable under ARAT buses, when we use the NRNT bus and the model check the temporal formula above with the ARAT MSI variant, the model checker will run into paths that don't satisfy ARAT, invoking unreachable transitions in the protocol and cause deadlock. 

The problem occurs with `[]A => []B` kinds of statements, where `[]A` is the assumption of the model, in our case ARAT/NRAT. Generally, the model checker can't know if `[]A` holds or not until running the state machine to the end, which means it can't quit early and stop exploring the paths that `[]A` is false; If the behavior of the model is only defined for paths that `[]A` holds, the model checker will induce undefined behaviors. On the other side, the model has no reason to consider transitions outside its designed assumptions, thus forcing us to incorporate the model assumptions into the overall state machine, rather than sharing a bigger state space and checking for `[]A => []B` kinds of formulas.

Recall our discussion about writing a single statement equal to the ARAT/NRAT property. Even if we come up with such a statement `[]ARAT` that holds if and only if the bus has the property, checking for `[]ARAT => []Coherence` will end up in a deadlock. To avoid deadlock, we must incorporate the property into explicit state machine transition rules for the bus, which means the bus we describe is highly concrete and couldn't represent any ARAT buses. In conclusion, it's hard, if even possible, to check "this MSI protocol works under **any** ARAT buses" without specifying the undefined behaviors.

One possible approach is to suppose that if the model deadlock then ARAT doesn't hold, so we can still use a general bus model, check for `[]ARAT => []Coherence`, and discard those deadlock paths. But it has 2 problems too. First, the assumption itself is not obvious, thus requiring to prove or a derived model checking. Second, reaching deadlock is too late to realize ARAT doesn't hold, we much prevent deadlock beforehand. But preventing deadlock explicitly in the state machine in turn means that the bus model must be ARAT thus not general enough.

In the end, we used `Spec == Init /\ [][Next /\ atomicRequest]_vars` and model check for `[]Coherence`. 

### TLA+ as a language

Since all 3 variants share the basic MSI idea, we want to reuse code as much as possible and separate the protocol state machines with bus models if possible. However, we ended up copy paste a lot more than we intended to. The main reason is that TLA+ lacks polymorphism, which means we can't use an interface as a placeholder to model the high-level structure of the MSI protocol and fill the detailed implementation in variant-specific files.

The `UNCHANGED` clause of the TLA+ also impeded our code reuse effort. As we introduce more variables in a new variant, we must include it in every old function that doesn't change the new variable. If we write the `UNCHANGED` clause outside the function, it becomes the boilerplate code itself. We searched for the reason that the designer of TLA+ enforce the `UNCHANGED` clause, he said that by requiring explicitly listing unchanged variables, he could avoid many bugs about unintentionally changing a variable. However, some users suggest making this clause optional and identifying unchanged variables automatically. 


## References
- [1] Sorin D J, Hill M D, Wood D A. A primer on memory consistency and cache coherence[J]. Synthesis lectures on computer architecture, 2011, 6(3): 1-212.
