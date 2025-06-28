rmState_msgs, tmState_tmPrepared
Round 8
java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  240.58s user 14.52s system 169% cpu 2:30.53 total

rmState_msgs: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  922.65s user 74.01s system 425% cpu 3:54.03 total 
tmState_tmPrepared: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  350.30s user 24.10s system 411% cpu 1:30.98 total

### Carini + MaxEndive = 384.6 seconds
### !CurrentWorstTime!

Notes:
Manually pruned 3 fluent variables
Goofy ah inductive invariants. Garbage decomposition, never do this
