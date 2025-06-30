rmState, rest

Round 6

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  132.00s user 8.02s system 160% cpu 1:27.35 total


msgs_tmPrepared, tmState, rmState.inv

Round 6

java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar       184.55s user 12.70s system 161% cpu 2:02.11 total


rmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  162.60s user 11.17s system 483% cpu 35.946 total

msgs_tmPrepared: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  336.84s user 17.21s system 486% cpu 1:12.77 total

tmState: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  156.00s user 8.42s system 475% cpu 34.603 total

### Carini(rmState, rest) + Carini(msgs_tmPrepared, tmState) + MaxEndive = 282.2

Notes:

needed \forall \exists \forall for msgs_tmPrepared, contributing to its lengthy runtime. Maybe if a less complicated triple decomposition needs only \forall \forall.
