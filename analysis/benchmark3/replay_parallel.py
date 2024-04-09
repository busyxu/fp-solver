"""

./replay.sh blas > replay_blas.out 2>&1 & disown
./replay.sh cdf > replay_cdf.out 2>&1 & disown
./replay.sh compAndopt > replay_compAndopt.out 2>&1 & disown
./replay.sh complex > replay_complex.out 2>&1 & disown
./replay.sh diffAndInteg > replay_diffAndInteg.out 2>&1 & disown
./replay.sh elementary > replay_elementary.out 2>&1 & disown
./replay.sh sf > replay_sf.out 2>&1 & disown
./replay.sh solveEqu > replay_solveEqu.out 2>&1 & disown

"""


import multiprocessing
import subprocess


def runOneTestCase(workDic):
    cmdStr = ["./replay1.sh", workDic, ">", f"replay_{workDic}.out", "2>&1", "&", "disown"]
    process = subprocess.Popen(" ".join(cmdStr), shell=True, executable="/bin/bash")
    pid = process.pid
    print(f"Task for {workDic} started in the background. PID: {pid}")
    

def main():
    testList = ["blas", "cdf", "compAndopt", "complex", "diffAndInteg", "elementary", "sf", "solveEqu"]
    cnt = 0
    pool = multiprocessing.Pool(processes=8)

    for workDic in testList:
        pool.apply_async(runOneTestCase, (workDic,))
        cnt += 1

    pool.close()
    pool.join()

    print("======>total:", cnt)


if __name__ == '__main__':
    main()
    print("======end======")
