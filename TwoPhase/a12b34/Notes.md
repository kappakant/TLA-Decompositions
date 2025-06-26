rmState_msgs, tmState_tmPrepared
Round 8
java -jar /Users/johnnguyen/Desktop/TLA/carini/bin/assump-synth.jar     none  240.58s user 14.52s system 169% cpu 2:30.53 total

rmState_msgs: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  198.94s user 15.14s system 539% cpu 39.660 total
tmState_tmPrepared: python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  350.30s user 24.10s system 411% cpu 1:30.98 total
MaxTime: 1:30.98 total

Carini + MaxTime = 4:01.51
Notes:
NumRandElements = 5
Manually pruned 3 fluent variables
II for CandSep is conjunction of 9 formulae excluding CandSep. Not exactly intuitive
I1, I2 verified by TLC of random subsets
