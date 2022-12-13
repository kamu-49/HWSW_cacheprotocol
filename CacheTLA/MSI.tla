-------------------------------- MODULE MSI --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT CoreNum, MaxWrite

Cores == 1..CoreNum
memory == 0
Storage == Cores \union {memory}

Data == 0..MaxWrite

VARIABLES state, data, bus, queue

vars == << state, data, bus, queue >>

Init == (* Global variables *)
        /\ state = [c \in Storage |-> IF c \in Cores THEN "I" ELSE "IorS"]
        /\ data = [c \in Storage |-> 0]
        /\ bus = [type |-> "Data", data |-> 0, sender |-> memory, receivers |-> {}]
        /\ queue = {}

-----------------

isData(msg) == msg.type \in {"Data", "NoData"}

isRequest(msg) == ~isData(msg)

nextMessage ==
    /\ bus.receivers = {}
    /\ queue # {}
    
updateBus ==
    /\ \E message \in queue:
        /\ bus' = message
        /\ queue' = queue \ {message}
    /\ UNCHANGED << state, data >>
    
updateData(entity, newData) ==
    data' = [data EXCEPT![entity] = newData]

updateState(entity, newState) ==
    state' = [state EXCEPT![entity] = newState]
    
send(msg) == 
    \*/\ \A m \in queue: m.sender # msg.sender
    /\ queue' = queue \union {msg}

sendData(from, to) ==
    send([type |-> "Data",
          data |-> data[from],
          sender |-> from,
          receivers |-> to])

sendNoData == 
    send([type |-> "NoData",
          receivers |-> {memory}])

sendMsg(msg, from) ==
    send([type |-> msg,
          sender |-> from,
          receivers |-> Storage])

trans(entity, prevState, message, isOwn, nextState) ==
    /\ state[entity] = prevState
    /\ bus.type = message
    /\ \/ (bus.sender = entity) = isOwn
       \/ message = "Data"
    /\ updateState(entity, nextState)
    
memoryTrans(prevState, message, nextState) ==
    trans(memory, prevState, message, FALSE, nextState)
    
updateBusReceivers(entity) ==
    /\ entity \in bus.receivers
    /\ bus' = [bus EXCEPT!.receivers = bus.receivers \ {entity}]

write(core) ==
    /\ state[core] = "M"
    /\ data[core] < MaxWrite
    /\ updateData(core, data[core] + 1)
    /\ UNCHANGED << state, bus, queue >>

------------------

cacheCoherence ==
    /\ \A c \in Cores :
        state[c] \in {"S", "M"} => data[c] >= data[memory]
    /\ \A c1, c2 \in Cores :
        state[c1] \in {"S", "M"} => data[c1] >= data[c2]

atomicRequest ==
    /\ Cardinality(queue') <= 1
    /\ isRequest(bus) => (\A msg \in queue': isData(msg))

atomicTransaction ==
    /\ Cardinality({msg \in queue': isData(msg)}) <= 1
    /\ (Cardinality(queue') < Cardinality(queue) /\ isRequest(bus)) => \A msg \in queue': isRequest(msg)


=============================================================================
\* Modification History
\* Last modified Sun Dec 11 20:57:16 EST 2022 by hq990
\* Created Wed Nov 23 20:34:22 EST 2022 by hq990
