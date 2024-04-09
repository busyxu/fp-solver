# 打开文本文件
with open('res_all.txt', 'r') as file:
    lines = file.readlines()

# 用于存储每行的第一个子串
first_substrings = set()

# 遍历文本内容并判断第一个子串是否相同
for i, line in enumerate(lines):
    # 使用逗号分割字符串并获取第一个子串
    parts = line.strip().split(',')
    if len(parts) > 0:
        first_substring = parts[0]
        if first_substring in first_substrings:
            print(f"第一个子串 '{first_substring}' 在行 {i+1} 和之前的某一行相同")
        else:
            first_substrings.add(first_substring)
