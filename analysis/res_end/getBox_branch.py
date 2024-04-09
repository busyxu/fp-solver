import matplotlib.pyplot as plt
import pandas as pd
import csv

'''
Get Data
'''

elementary_bfs_dict = {}
elementary_dfs_dict = {}
complex_bfs_dict = {}
complex_dfs_dict = {}
diffAndInteg_bfs_dict = {}
diffAndInteg_dfs_dict = {}
blas_bfs_dict = {}
blas_dfs_dict = {}
algorithm_bfs_dict = {}
algorithm_dfs_dict = {}
solveEqu_bfs_dict = {}
solveEqu_dfs_dict = {}
compAndopt_bfs_dict = {}
compAndopt_dfs_dict = {}
sf_bfs_dict = {}
sf_dfs_dict = {}


def sub_func(strList, searchType, driverName, solverType, bfsdatadict, dfsdatadict):
    coverage = "0"
    coverLine = "0"
    time = "0"
    if len(strList) >= 5:
        if strList[1].strip() != "":
            coverage = strList[1].strip()
        # else:
        #     coverage = str(0)
        if strList[3].strip() != "":
            coverLine = strList[3].strip()
        # else:
        #     coverLine = str(0)
        if strList[4].strip() != "":
            time = strList[3].strip()
        # else:
        #     time = str(0)

    if searchType == "bfs":
        if bfsdatadict.get(driverName) is None:
            bfsdatadict[driverName] = [0] * 9  # smt bitwuzla mathsat5 dreal-is cvc5-real fp2int jfs gosat smt-dreal smt-jfs
        if solverType == "smt":
            bfsdatadict[driverName][0] = coverLine
        if solverType == "bitwuzla":
            bfsdatadict[driverName][1] = coverLine
        if solverType == "mathsat5":
            bfsdatadict[driverName][2] = coverLine
        if solverType == "dreal-is":
            bfsdatadict[driverName][3] = coverLine
        if solverType == "cvc5-real":
            bfsdatadict[driverName][4] = coverLine
        if solverType == "fp2int":
            bfsdatadict[driverName][5] = coverLine
        if solverType == "jfs":
            bfsdatadict[driverName][6] = coverLine
        if solverType == "gosat":
            bfsdatadict[driverName][7] = coverLine
        if solverType == "smt-dreal":
            bfsdatadict[driverName][8] = coverLine
        # if solverType == "smt-jfs":
        #     bfsdatadict[driverName][9] = coverLine

    if searchType == "dfs":
        if dfsdatadict.get(driverName) is None:
            dfsdatadict[driverName] = [0] * 9  # smt bitwuzla mathsat5 dreal-is cvc5-real fp2int jfs gosat smt-dreal smt-jfs
        if solverType == "smt":
            dfsdatadict[driverName][0] = coverLine
        if solverType == "bitwuzla":
            dfsdatadict[driverName][1] = coverLine
        if solverType == "mathsat5":
            dfsdatadict[driverName][2] = coverLine
        if solverType == "dreal-is":
            dfsdatadict[driverName][3] = coverLine
        if solverType == "cvc5-real":
            dfsdatadict[driverName][4] = coverLine
        if solverType == "fp2int":
            dfsdatadict[driverName][5] = coverLine
        if solverType == "jfs":
            dfsdatadict[driverName][6] = coverLine
        if solverType == "gosat":
            dfsdatadict[driverName][7] = coverLine
        if solverType == "smt-dreal":
            dfsdatadict[driverName][8] = coverLine
        # if solverType == "smt-jfs":
        #     bfsdatadict[driverName][9] = coverLine


def input_data():
    # 文本文件的路径
    txt_file = 'res_all_1.txt'

    # 打开文件并逐行读取内容
    with open(txt_file, 'r') as file:
        lines = file.readlines()

    # 遍历每一行内容
    for line in lines:
        strList = line.split(",")
        strName = strList[0].strip().split("&")
        className = strName[0]
        driverName = strName[1]
        solverType = strName[2]
        searchType = strName[3][:3]

        if className == "elementary":
            sub_func(strList, searchType, driverName, solverType, elementary_bfs_dict, elementary_dfs_dict)
        # elif className == "complex":
        #     sub_func(strList, searchType, driverName, solverType, complex_bfs_dict, complex_dfs_dict)
        # elif className == "diffAndInteg":
        #     sub_func(strList, searchType, driverName, solverType, diffAndInteg_bfs_dict, diffAndInteg_dfs_dict)
        # elif className == "blas":
        #     sub_func(strList, searchType, driverName, solverType, blas_bfs_dict, blas_dfs_dict)
        elif className == "algorithm":
            sub_func(strList, searchType, driverName, solverType, algorithm_bfs_dict, algorithm_dfs_dict)
        # elif className == "solveEqu":
        #     sub_func(strList, searchType, driverName, solverType, solveEqu_bfs_dict, solveEqu_dfs_dict)
        # elif className == "compAndopt":
        #     sub_func(strList, searchType, driverName, solverType, compAndopt_bfs_dict, compAndopt_dfs_dict)
        elif className == "sf":
            sub_func(strList, searchType, driverName, solverType, sf_bfs_dict, sf_dfs_dict)

        # # 处理每一行内容，这里只是打印示例
        # print(line.strip())  # 使用 .strip() 去除每行末尾的换行符


def write_date(datadict, csvname):

  input_data()

  # CSV文件的路径
  csv_file = "csv_branch_1/"+csvname

  # 写入CSV文件
  with open(csv_file, 'w', newline='') as file:
      writer = csv.writer(file)

      for key in datadict.keys():
          str = []
          str.append(key)
          for v in datadict[key]:
              str.append(v)
          # res = key+','+','.join(str)
          writer.writerows([str])

  print(f'数据已写入CSV文件: {csv_file}')


input_data()


# # solver_type = ["smt", "bitwuzla", "mathsat5", "cvc5-real", "dreal-is", "fp2int", "jfs", "gosat", "smt-dreal", "smt-jfs"]
# solver_type = ["smt", "bitwuzla", "mathsat5", "cvc5-real", "dreal-is", "jfs", "gosat", "smt-dreal", "smt-jfs"]
# for stype in solver_type:
#     cur_dict =
#     write_date(elementary_bfs_dict, stype+"_bfs_dict_output.csv")
#     write_date(elementary_dfs_dict, stype+"_dfs_dict_output.csv")

write_date(elementary_bfs_dict, "elementary_bfs_dict_output.csv")
# write_date(complex_bfs_dict, "complex_bfs_dict_output.csv")
# write_date(diffAndInteg_bfs_dict, "diffAndInteg_bfs_dict_output.csv")
# # write_date(blas_bfs_dict, "blas_bfs_dict_output.csv")
write_date(algorithm_bfs_dict, "algorithm_bfs_dict_output.csv")
# write_date(solveEqu_bfs_dict, "solveEqu_bfs_dict_output.csv")
# write_date(compAndopt_bfs_dict, "compAndopt_bfs_dict_output.csv")
write_date(sf_bfs_dict, "sf_bfs_dict_output.csv")

write_date(elementary_dfs_dict, "elementary_dfs_dict_output.csv")
# write_date(complex_dfs_dict, "complex_dfs_dict_output.csv")
# write_date(diffAndInteg_dfs_dict, "diffAndInteg_dfs_dict_output.csv")
# # write_date(blas_dfs_dict, "blas_dfs_dict_output.csv")
write_date(algorithm_dfs_dict, "algorithm_dfs_dict_output.csv")
# write_date(solveEqu_dfs_dict, "solveEqu_dfs_dict_output.csv")
# write_date(compAndopt_dfs_dict, "compAndopt_dfs_dict_output.csv")
write_date(sf_dfs_dict, "sf_dfs_dict_output.csv")

'''
Draw Box
'''

meanAll = []


def drawfigure(incsvfile, outfilename):
    z3List = []
    bitwuzlaList = []
    mathsat5List = []

    drealList = []
    cvc5List = []

    fp2intList = []
    jfsList = []

    gosatList = []

    synergyList = []

    # smtJfsList = []

    with open("csv_branch_1/"+incsvfile, 'r') as f:
        for line in f:
            if "gsl_" not in line:
                continue

            testName, z3, bitwuzla , mathsat5, dreal, cvc5real, fp2int, jfs, gosat, synergy = line.split(",")
            testName = testName.replace(" ", "")

            if len(z3) > 0: # 说明有z3 的信息
                z3List.append(int(z3))
            else:
                z3List.append(0)
            if len(bitwuzla) > 0:
                bitwuzlaList.append(int(bitwuzla))
            else:
                bitwuzlaList.append(0)
            if len(mathsat5) > 0:
                mathsat5List.append(int(mathsat5))
            else:
                mathsat5List.append(0)
            if len(dreal) > 0:
                drealList.append(int(dreal))
            else:
                drealList.append(0)
            if len(cvc5real) > 0:
                cvc5List.append(int(cvc5real))
            else:
                cvc5List.append(0)
            if len(fp2int) > 0:
                fp2intList.append(int(fp2int))
            else:
                fp2intList.append(0)
            if len(jfs) > 0:
                jfsList.append(int(jfs))
            else:
                jfsList.append(0)
            if len(gosat) > 0:
                gosatList.append(int(gosat))
            else:
                gosatList.append(0)
            if len(synergy) > 0:
                synergyList.append(int(synergy))
            else:
                synergyList.append(0)
            # if len(smt_jfs) > 0:
            #     smtJfsList.append(int(smt_jfs))
            # else:
            #     smtJfsList.append(0)

    plt.figure(dpi=1080, figsize=(10, 9))

    # merged_array = [max(a, b) for a, b in zip(z3List, bitwuzlaList, synergyList)]
    mergedList = [max(values) for values in
                  zip(z3List, bitwuzlaList, mathsat5List, drealList, cvc5List, fp2intList, jfsList, gosatList,
                      synergyList)]

    import numpy as np
    z3avg = np.mean(np.array(z3List))
    bitwuzlaavg = np.mean(np.array(bitwuzlaList))
    mathsat5avg = np.mean(np.array(mathsat5List))
    drealavg = np.mean(np.array(drealList))
    cvc5avg = np.mean(np.array(cvc5List))
    fp2intavg = np.mean(np.array(fp2intList))
    jfsavg = np.mean(np.array(jfsList))
    gosatavg = np.mean(np.array(gosatList))
    synergyavg = np.mean(np.array(synergyList))
    # synergyavg = np.mean(np.array(mergedList))
    # smtJfsavg = np.mean(np.array(smtJfsList))
    # print(synergyList)
    # meanAll.append([z3avg, bitwuzlaavg, mathsat5avg, drealavg, cvc5avg, fp2intavg, jfsavg, gosatavg, synergyavg, smtJfsavg])
    meanAll.append(
        [z3avg, bitwuzlaavg, mathsat5avg, drealavg, cvc5avg, fp2intavg, jfsavg, gosatavg, synergyavg])

    data = pd.DataFrame({
      "BVFP\n(Z3)": z3List,
      "BVFP\n(Bitwuzla)": bitwuzlaList,
      "BVFP\n(MathSAT5)": mathsat5List,
      "RSO\n(dReal)": drealList,
      "RSO\n(CVC5)": cvc5List,
      "ISC\n(Z3)": fp2intList,
      "FUZZ\n(JFS)": jfsList,
      "Search\n(goSAT)": gosatList,
      # "Synergy": mergedList
      "Synergy": synergyList,
      # "SmtJfs": smtJfsList
    })

    #draw
    data.boxplot(fontsize=12)
    plt.ylabel("NoBC", fontsize=16)
    # plt.xlabel("(a) BFS Result",fontsize=28,labelpad=20)
    #plt.show()

    # plt.savefig("dfs_boxplot_yx.pdf")
    plt.savefig("pdf_branch_1/"+outfilename)
    plt.close()

drawfigure("elementary_bfs_dict_output.csv", "elementary_bfs_box_b.pdf")
drawfigure("elementary_dfs_dict_output.csv", "elementary_dfs_box_b.pdf")
#
# drawfigure("complex_bfs_dict_output.csv", "complex_bfs_box.pdf")
# drawfigure("complex_dfs_dict_output.csv", "complex_dfs_box.pdf")
#
# drawfigure("diffAndInteg_bfs_dict_output.csv", "diffAndInteg_bfs_box.pdf")
# drawfigure("diffAndInteg_dfs_dict_output.csv", "diffAndInteg_dfs_box.pdf")
#
# # # drawfigure("blas_bfs_dict_output.csv", "blas_bfs_box.pdf")
# # # drawfigure("blas_dfs_dict_output.csv", "blas_dfs_box.pdf")
#
drawfigure("algorithm_bfs_dict_output.csv", "algorithm_bfs_box_b.pdf")
drawfigure("algorithm_dfs_dict_output.csv", "algorithm_dfs_box_b.pdf")
#
# drawfigure("solveEqu_bfs_dict_output.csv", "solveEqu_bfs_box.pdf")
# drawfigure("solveEqu_dfs_dict_output.csv", "solveEqu_dfs_box.pdf")
#
# drawfigure("compAndopt_bfs_dict_output.csv", "compAndopt_bfs_box.pdf")
# drawfigure("compAndopt_dfs_dict_output.csv", "compAndopt_dfs_box.pdf")

drawfigure("sf_bfs_dict_output.csv", "sf_bfs_box_b.pdf")
drawfigure("sf_dfs_dict_output.csv", "sf_dfs_box_b.pdf")

# CSV文件的路径
mean_file = "mean_branch_1.txt"
# 写入CSV文件
with open(mean_file, 'w', newline='') as file:
    writer = csv.writer(file)

    for v in meanAll:
        writer.writerows([v])

print(f'数据已写入mean.txt: {mean_file}')