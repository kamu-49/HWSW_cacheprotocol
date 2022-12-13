# Formal Verifications in Cache Protocols

Hello. This is Cam and Qiao's hardware and software project. We will be using software in order to simulate the verification of cache protocols using model checking. This README will be updated with updates on our project for communication as well as links that we will use to help with our steps moving forward.



## Protocols to verify

A collection of classic protocols from Wiki: <https://en.wikipedia.org/wiki/Cache_coherency_protocols_(examples)#Coherency_protocols>

> Note: Many of the following protocols have only historical value. At the present the main protocols used are R-MESI type / MESIF and HRT-ST-MES (MOESI type) or a subset of this.

An interesting 2021 protocol: [Designing Predictable Cache Coherence Protocols for Multi-Core Real-Time Systems](https://ieeexplore-ieee-org.ezproxy.cul.columbia.edu/document/9258378)
 
## Methods
- Professor's suggestion of using TLA+: <https://lamport.azurewebsites.net/pubs/fm99.pdf>
- Rumur: <https://github.com/Smattr/rumur>
- SPIN

## Updates
### Cam 11.20
Currently am using MobaxTerm for the majority of the things that I need to be implemented as stated in the Rumur page. An important link for implementing plugins is below:
- MobaxTerm plugins: <https://mobaxterm.mobatek.net/plugins.html>
- MObaxTerm plugin help: <https://stackoverflow.com/questions/16746251/how-to-install-plugin-for-mobaxterm>

### Qiao 11.20
Searching for tutorials about TLA+ and its model checkers.
- Introduction to TLA+ and beginner's guide: <https://old.learntla.com/introduction/>

### Qiao 11.23
Trying to write TLA+ code for cache protocols.
- An example of verifying cache protocol with TLA+: <https://github.com/ease-lab/1Update>

### Qiao 11.25
- Upload TLA+/PlusCal scratch for the simple MSI protocol (In progress)
- Another tutorial on TLA+ and PlusCal: <https://www.learntla.com/core/index.html>


## Status Report 11.30
- Install TLA+ toolbox
- Model MSI cache protocol using TLA+
- Write properties and run the model checker (In progress)

### Qiao 12.1
- A detailed guide for cache coherence protocols (containing complete state transition rules): <https://course.ece.cmu.edu/~ece847c/S15/lib/exe/fetch.php?media=part2_2_sorin12.pdf>

### Cam 12.5
- Finally finally figured out Rumur. Added Ubuntu through Microsoft. No longer need the flex and rumur attepmted installation. Will focus onlearning more about Rumur with Ubuntu and how to properly create output files (Rumur will only proplery run with a given output file). Will also switch between that and helping with TLA stuff with Qiao

### Qiao 12.12
- Finish TLA+ modules
