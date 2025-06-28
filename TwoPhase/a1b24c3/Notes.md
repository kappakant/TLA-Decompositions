rmState, rest

Round 6

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  132.00s user 8.02s system 160% cpu 1:27.35 total


msgs_tmPrepared, tmState

Round 5

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar       220.65s user 13.25s system 153% cpu 2:32.34 total

rmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  162.60s user 11.17s system 483% cpu 35.946 total

msgs_tmPrepared: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  238.39s user 12.30s system 500% cpu 50.084 total

tmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  94.89s user 6.30s system 545% cpu 18.536 total

### Carini(rmState, rest) + Carini(msgs_tmPrepared, tmState) + MaxEndive = 290 seconds
### Longer than a124b3; MaxEndive is significantly smaller, but Carini(msgs_tmPrepared, tmState) is surprisingly long despite taking one less round.
