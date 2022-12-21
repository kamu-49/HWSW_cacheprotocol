------------------------------ MODULE MSI_SplitTransactionBus ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT CoreNum, MaxWrite

Cores == 1..CoreNum
memory == 0
Storage == Cores \union {memory}

Data == 0..MaxWrite

CState == {"I", "IS^AD", "IS^D", "IS^A", "IM^AD", "IM^D", "IM^A", "S", "SM^AD", "SM^D", "SM^A", "M", "MI^A", "II^A"}
MState == {"IorS", "IorS^D", "IorS^A", "M"}

MessageR == [type: {"GetS", "GetM", "PutM"},
             sender: Cores,
             receivers: SUBSET Storage]

MessageD == [type: {"Data"},
             data: Data,
             sender: Storage,
             receivers: SUBSET Storage]

VARIABLES state, data, busR, busD, owner

vars == << state, data, busR, busD, owner >>

Init == (* Global variables *)
        /\ state = [c \in Storage |-> IF c \in Cores THEN "I" ELSE "IorS"]
        /\ data = [c \in Storage |-> 0]
        /\ busR = << >>
        /\ busD = << >>
        /\ owner = memory

---------------------------------------------------

isData(msg) == msg.type \in {"Data"}

isRequest(msg) == ~isData(msg)

noCurrentMsg == 
    /\ Len(busR) = 0 \/ Head(busR).receivers = {}
    /\ Len(busD) = 0 \/ Head(busD).receivers = {}
    
nextMessage ==
    /\ noCurrentMsg
    /\ Len(busR) + Len(busD) > 0
    
updateBus(bus) ==
    /\ Len(bus) > 0
    /\ Head(bus).receivers = {}
    /\ bus' = SubSeq(bus, 2, Len(bus))
    
updateEitherBus == 
    \/ /\ updateBus(busR)
       /\ UNCHANGED << state, data, busD, owner >>
    \/ /\ updateBus(busD)
       /\ UNCHANGED << state, data, busR, owner >>
    
updateData(entity, newData) ==
    data' = [data EXCEPT![entity] = newData]

updateState(entity, newState) ==
    state' = [state EXCEPT![entity] = newState]
    
send(msg, bus) ==
    bus' = Append(bus, msg)

sendData(from, to) ==
    send([type |-> "Data",
          data |-> data[from],
          sender |-> from,
          receivers |-> to],
         busD)

sendMsg(msg, from) ==
    /\ Len(busR) = 0
    /\ send([type |-> msg,
             sender |-> from,
             receivers |-> Storage],
            busR)

trans(entity, prevState, message, isOwn, nextState) ==
    /\ state[entity] = prevState
    /\ IF message = "Data"
       THEN /\ Len(busD) > 0
            /\ Head(busD).type = message
       ELSE /\ Len(busR) > 0
            /\ Head(busR).type = message
            /\ (Head(busR).sender = entity) = isOwn
    /\ updateState(entity, nextState)
    
memoryTrans(prevState, message, nextState) ==
    trans(memory, prevState, message, FALSE, nextState)
    
memoryTransPutM(prevState, isOwner, nextState) ==
    /\ state[memory] = prevState
    /\ Len(busR) > 0
    /\ Head(busR).type = "PutM"
    /\ (Head(busR).sender = owner) = isOwner
    /\ updateState(memory, nextState)
    
updateBusReceivers(bus, entity) ==
    /\ Len(bus) > 0
    /\ entity \in Head(bus).receivers
    /\ bus' = [bus EXCEPT![1].receivers = bus[1].receivers \ {entity}]

write(core) ==
    /\ state[core] = "M"
    /\ data[core] < MaxWrite
    /\ updateData(core, data[core] + 1)
    /\ UNCHANGED << state, busR, busD, owner >>

--------------------

coreBusEvent(core) ==
     \/ /\ updateBusReceivers(busD, core)
        /\ updateData(core, Head(busD).data)
        /\ \/ trans(core, "IS^D", "Data", TRUE, "S")
           \/ trans(core, "IM^D", "Data", TRUE, "M")
           \/ trans(core, "SM^D", "Data", TRUE, "M")
           \/ trans(core, "IS^AD", "Data", TRUE, "IS^A")
           \/ trans(core, "IM^AD", "Data", TRUE, "IM^A")
           \/ trans(core, "SM^AD", "Data", TRUE, "SM^A")
        /\ UNCHANGED << busR, owner >>
     \/ /\ updateBusReceivers(busR, core)
        /\ \/ /\
                   \/ trans(core, "I", "GetS", FALSE, "I")
                   \/ trans(core, "I", "GetM", FALSE, "I")
                   \/ trans(core, "I", "PutM", FALSE, "I")
                   
                   \/ trans(core, "IS^AD", "GetS", TRUE, "IS^D")
                   \/ trans(core, "IS^AD", "GetM", TRUE, "IS^D")
                   \/ trans(core, "IS^AD", "GetS", FALSE, "IS^AD")
                   \/ trans(core, "IS^AD", "GetM", FALSE, "IS^AD")
                   \/ trans(core, "IS^AD", "PutM", FALSE, "IS^AD")
                   
                   \/ trans(core, "IS^D", "GetS", FALSE, "IS^D")
                   \* \/ trans(core, "IS^D", "GetM", FALSE, "IS^D")
                   
                   \/ trans(core, "IS^A", "GetS", TRUE, "S")
                   \/ trans(core, "IS^A", "GetM", TRUE, "S")
                   \/ trans(core, "IS^A", "GetS", FALSE, "IS^A")
                   \/ trans(core, "IS^A", "GetM", FALSE, "IS^A")
                   
                   \/ trans(core, "IM^AD", "GetM", TRUE, "IM^D")
                   \/ trans(core, "IM^AD", "GetS", FALSE, "IM^AD")
                   \/ trans(core, "IM^AD", "GetM", FALSE, "IM^AD")
                   \/ trans(core, "IM^AD", "PutM", FALSE, "IM^AD")
                   
                   \* \/ trans(core, "IM^D", "GetS", FALSE, "IM^D")
                   \* \/ trans(core, "IM^D", "GetM", FALSE, "IM^D")
                   
                   \/ trans(core, "IM^A", "GetM", TRUE, "M")
                   \/ trans(core, "IM^A", "GetS", FALSE, "IM^A")
                   \/ trans(core, "IM^A", "GetM", FALSE, "IM^A")
                   
                   \/ trans(core, "S", "GetS", FALSE, "S")
                   \/ trans(core, "S", "GetM", FALSE, "I")
                   
                   \/ trans(core, "SM^AD", "GetM", TRUE, "SM^D")
                   \/ trans(core, "SM^AD", "GetS", FALSE, "SM^AD")
                   \/ trans(core, "SM^AD", "GetM", FALSE, "IM^AD")
                   
                   \* \/ trans(core, "SM^D", "GetS", FALSE, "SM^D")
                   \* \/ trans(core, "SM^D", "GetM", FALSE, "SM^D")
                   
                   \/ trans(core, "SM^A", "GetM", TRUE, "M")
                   \/ trans(core, "SM^A", "GetS", FALSE, "SM^A")
                   \/ trans(core, "SM^A", "GetM", FALSE, "IM^A")
                   
                   \/ trans(core, "II^A", "PutM", TRUE, "I")
                   \/ trans(core, "II^A", "GetS", FALSE, "II^A")
                   \/ trans(core, "II^A", "GetM", FALSE, "II^A")
                   \/ trans(core, "II^A", "PutM", FALSE, "II^A")
              /\ UNCHANGED << data, busD, owner >>
           \/ /\
                   \/ /\ trans(core, "M", "GetS", FALSE, "S")
                      /\ sendData(core, {memory, Head(busR).sender})
                   \/ /\ trans(core, "M", "GetM", FALSE, "I")
                      /\ sendData(core, {Head(busR).sender})
                   \/ /\ trans(core, "MI^A", "PutM", TRUE, "I")
                      /\ sendData(core, {memory})
                   \/ /\ trans(core, "MI^A", "GetS", FALSE, "II^A")
                      /\ sendData(core, {memory, Head(busR).sender})
                   \/ /\ trans(core, "MI^A", "GetM", FALSE, "II^A")
                      /\ sendData(core, {Head(busR).sender})
              /\ UNCHANGED << data, owner >>

memoryBusEvent ==
     \/ /\ updateBusReceivers(busD, memory)
        /\ \/ /\ memoryTrans("IorS^D", "Data", "IorS")
              /\ updateData(memory, Head(busD).data)
           \/ /\ memoryTrans("M", "Data", "IorS^A")
              /\ updateData(memory, Head(busD).data)
        /\ UNCHANGED << busR, owner >>
     \/ /\ updateBusReceivers(busR, memory)
        /\ 
           \/ /\ 
                 \/ memoryTransPutM("IorS", FALSE, "IorS")
                 \/ memoryTransPutM("M", FALSE, "M")
                 \* \/ memoryTrans("IorS^D", "GetS", "IorS^D")
                 \* \/ memoryTrans("IorS^D", "GetM", "IorS^D")
                 \/ memoryTransPutM("IorS^D", TRUE, "IorS^D")
                 \/ memoryTransPutM("IorS^D", FALSE, "IorS^D")
                 \/ memoryTrans("IorS^A", "GetM", "IorS^A")
                 \/ memoryTransPutM("IorS^A", FALSE, "IorS^A")
              /\ UNCHANGED << data, busD, owner >>
           \/ /\
                 \/ /\ memoryTrans("M", "GetS", "IorS^D")
                    /\ owner' = memory
                 \/ /\ memoryTrans("M", "GetM", "M")
                    /\ owner' = Head(busR).sender
                 \/ /\ memoryTransPutM("M", TRUE, "IorS^D")
                    /\ owner' = memory
                 \/ /\ memoryTrans("IorS^A", "GetS", "IorS")
                    /\ owner' = memory
                 \/ /\ memoryTransPutM("IorS^A", TRUE, "IorS")
                    /\ owner' = memory
              /\ UNCHANGED << data, busD >>
           \/ /\ memoryTrans("IorS", "GetS", "IorS")
              /\ sendData(memory, {Head(busR).sender})
              /\ UNCHANGED << data, owner >>
           \/ /\ memoryTrans("IorS", "GetM", "M")
              /\ owner' = Head(busR).sender
              /\ sendData(memory, {Head(busR).sender})
              /\ UNCHANGED << data >>
    
getS(core) ==
    /\ sendMsg("GetS", core)
    /\ state[core] = "I"
    /\ updateState(core, "IS^AD")
    /\ UNCHANGED << data, busD, owner >>
getM(core) ==
    /\ sendMsg("GetM", core)
    /\ \/ /\ state[core] = "I"
          /\ updateState(core, "IM^AD")
       \/ /\ state[core] = "S"
          /\ updateState(core, "SM^AD")
    /\ UNCHANGED << data, busD, owner >>
putM(core) ==
    /\ sendMsg("PutM", core)
    /\ state[core] = "M"
    /\ updateState(core, "MI^A")
    /\ UNCHANGED << data, busD, owner >>
---------------------------------------------------------

coreAction(core) ==
    \/ coreBusEvent(core)
    \/ getS(core)
    \/ getM(core)
    \/ putM(core)
    \/ /\ write(core)
       /\ UNCHANGED << state, busR, busD, owner >>

memoryAction == memoryBusEvent

Next == 
    \/ updateEitherBus
    \/ \E core \in Cores: coreAction(core)
    \/ memoryAction

typeInvariant == 
    /\ \A c \in Cores : state[c] \in CState
    /\ state[memory] \in MState
    /\ \A c \in Storage : data[c] \in Data
    /\ \A i \in 1..Len(busR) : busR[i] \in MessageR
    /\ \A i \in 1..Len(busD) : busD[i] \in MessageD
    /\ owner \in Storage

cacheCoherence ==
    /\ \A c \in Cores :
        state[c] \in {"S", "M"} => data[c] >= data[memory]
    /\ \A c1, c2 \in Cores :
        state[c1] \in {"S", "M"} => data[c1] >= data[c2]
        
Spec == Init /\ [][Next]_vars

Invariants == /\ typeInvariant
              /\ (noCurrentMsg => cacheCoherence)



=============================================================================
\* Modification History
\* Last modified Mon Dec 12 20:52:50 EST 2022 by hq990
\* Created Mon Dec 12 15:29:28 EST 2022 by hq990
