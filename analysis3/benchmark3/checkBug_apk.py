import os
import shutil

def search_and_copy_runlog_files(source_folder, target_folders, target_strings):
    # 初始化计数器字典，用于跟踪每个目标文件夹中的文件数量
    file_count = {target_folder: 0 for target_folder in target_folders}

    # 遍历源文件夹中的所有文件和子文件夹
    for root, dirs, files in os.walk(source_folder):
        for file in files:
            if file.endswith('.runlog'):
                file_path = os.path.join(root, file)
                with open(file_path, 'r') as f:
                    content = f.read()
                    for target_folder, target_string in zip(target_folders, target_strings):
                        if target_string in content:
                            # 构造目标文件路径
                            target_file_path = os.path.join(target_folder, file)
                            # 复制文件到目标文件夹
                            shutil.copy2(file_path, target_file_path)
                            print(f"Copied file '{file}' to '{target_folder}'")
                            # 增加目标文件夹的文件数量计数
                            file_count[target_folder] += 1

    # 打印每个目标文件夹的文件数量
    for target_folder, count in file_count.items():
        print(f"Found {count} files in '{target_folder}'")

# 目标文件夹和目标字符串列表
target_folders = ['../bug1_runlog', '../bug2_runlog', '../good_runlog']
target_strings = [
    'KLEE: WARNING: KLEE: watchdog exiting (no child)',
    'WARNING: KLEE: WATCHDOG: kill(9)ing child (I tried to be nice)',
    'KLEE: done: generated tests = '
]

# 调用函数并传入源文件夹路径、目标文件夹列表和目标字符串列表
search_and_copy_runlog_files('./', target_folders, target_strings)
