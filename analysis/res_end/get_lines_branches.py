import numpy as np
import csv

def get_data(txt_file):

    # txt_file = 'res_all_1.txt'

    dist_sum_lines = {'elementary_bfs': [0] * 9, 'elementary_dfs': [0] * 9, 'algorithm_bfs': [0] * 9,
                      'algorithm_dfs': [0] * 9, 'sf_bfs': [0] * 9, 'sf_dfs': [0] * 9}

    dist_sum_branches = {'elementary_bfs': [0] * 9, 'elementary_dfs': [0] * 9, 'algorithm_bfs': [0] * 9,
                      'algorithm_dfs': [0] * 9, 'sf_bfs': [0] * 9, 'sf_dfs': [0] * 9}

    with open(txt_file, 'r') as file:
        lines = file.readlines()
        for line in lines:
            strList = line.split(",")
            strName = strList[0].strip().split("&")
            className = strName[0]
            driverName = strName[1]
            solverType = strName[2]
            searchType = strName[3][:3]

            locc = 0
            if len(strList)>2 and strList[2].strip() != "":
                locc = int(strList[2].strip())
            else:
                print(line)

            nobc = 0
            if len(strList)>3 and strList[3].strip() != "":
                nobc = int(strList[3].strip())
            else:
                print(line)

            key = className+'_'+searchType
            if solverType == "smt":
                dist_sum_lines[key][0] += locc
                dist_sum_branches[key][0] += nobc
            if solverType == "bitwuzla":
                dist_sum_lines[key][1] += locc
                dist_sum_branches[key][1] += nobc
            if solverType == "mathsat5":
                dist_sum_lines[key][2] += locc
                dist_sum_branches[key][2] += nobc
            if solverType == "dreal-is":
                dist_sum_lines[key][3] += locc
                dist_sum_branches[key][3] += nobc
            if solverType == "cvc5-real":
                dist_sum_lines[key][4] += locc
                dist_sum_branches[key][4] += nobc
            if solverType == "fp2int":
                dist_sum_lines[key][5] += locc
                dist_sum_branches[key][5] += nobc
            if solverType == "jfs":
                dist_sum_lines[key][6] += locc
                dist_sum_branches[key][6] += nobc
            if solverType == "gosat":
                dist_sum_lines[key][7] += locc
                dist_sum_branches[key][7] += nobc
            if solverType == "smt-dreal":
                dist_sum_lines[key][8] += locc
                dist_sum_branches[key][8] += nobc

    return dist_sum_lines, dist_sum_branches


if __name__ == '__main__':

    # txt_file = 'res_all_1.txt'

    txt_files = ['res_all_1.txt', 'res_all3.txt']

    lines_lists = []
    branches_lists = []

    for txt_file in txt_files:
        dist_sum_lines, dist_sum_branches = get_data(txt_file)
        linesList = []
        branchesList = []
        for key in dist_sum_lines.keys():
            linesList.append(dist_sum_lines[key])
        for key in dist_sum_branches.keys():
            branchesList.append(dist_sum_branches[key])

        lines_lists.append(linesList)
        branches_lists.append(branchesList)

    mean_list_lines = np.mean(lines_lists, axis=0)
    std_list_lines = np.std(lines_lists, axis=0)
    mean_list_branches = np.mean(branches_lists, axis=0)
    std_list_branches = np.std(branches_lists, axis=0)
    print("LoCC mean:\n", mean_list_lines)
    print("LoCC std:\n", std_list_lines)
    print("NoBC mean:\n", mean_list_branches)
    print("NoBC std:\n", std_list_branches)


    write_data_lines = []
    for i in range(len(mean_list_lines)):
        temp = []
        for j in range(len(mean_list_lines[i])):
            element = str(mean_list_lines[i][j])+' ($\pm$'+str(std_list_lines[i][j])+')'
            temp.append(element)
        write_data_lines.append(temp)

    write_data_branches = []
    for i in range(len(mean_list_branches)):
        temp = []
        for j in range(len(mean_list_branches[i])):
            element = str(mean_list_branches[i][j]) + ' ($\pm$' + str(std_list_branches[i][j]) + ')'
            temp.append(element)
        write_data_branches.append(temp)

    csv_cov = "cov_mean_std.csv"
    with open(csv_cov, 'w', newline='') as file:
        writer = csv.writer(file)
        for v in write_data_lines:
            writer.writerows([v])
        for v in write_data_branches:
            writer.writerows([v])
    print(f'write lines into {csv_cov}.')
