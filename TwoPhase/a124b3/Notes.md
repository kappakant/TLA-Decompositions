rmState_msgs_tmPrepared, tmState

Round 6

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  209.03s user 12.83s system 167% cpu 2:12.29 total

rmState_msgs_tmPrepared: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 2000  538.17s user 28.77s system 559% cpu 1:41.38 total

tmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  94.89s user 6.30s system 545% cpu 18.536 total

### Carini + MaxEndive = 233.7 seconds

Notes: 
rmState_* needed endiiive to find an II. Very fussy decomposition it seems.
