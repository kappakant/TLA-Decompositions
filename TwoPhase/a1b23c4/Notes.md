rmState, rest

Round 6

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  132.00s user 8.02s system 160% cpu 1:27.35 total


msgs_tmState, tmPrepared, rmState.inv

Round 3

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar       63.88s user 4.02s system 157% cpu 43.064 total


rmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  162.60s user 11.17s system 483% cpu 35.946 total

msgs_tmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  163.97s user 8.44s system 519% cpu 33.174 total

tmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  80.72s user 4.31s system 531% cpu 16.008 total

### Carini(rmState, rest) + Carini(msgs_tmState, tmPrepared) + MaxEndive = 166.4 seconds
