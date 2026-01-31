#!/bin/bash
# Quick start: 验证第一个例子

echo "===== Step 1: 运行OCaml实现 ====="
cd "$(dirname "$0")/../../examples"

echo "Running 01_basic.sub..."
../../_build/default/src/sub_async/sub_async.exe 01_basic.sub > ../formalization/agda/traces/01_basic_trace.txt 2>&1

echo ""
echo "===== Step 2: 查看trace ====="
cat ../formalization/agda/traces/01_basic_trace.txt

echo ""
echo "===== Step 3: 在Agda中构造对应configuration ====="
echo "打开 Examples.agda 并根据上面的trace填充 example1-step1, example1-step2 等"

echo ""
echo "===== Step 4: 尝试证明第一步 ====="
echo "在Emacs/VS Code中："
echo "1. 打开 Examples.agda"
echo "2. 移动到 example1-step1-valid 的 {!!} hole"
echo "3. 按 C-c C-l (load file)"  
echo "4. 按 C-c C-, (查看hole的类型和上下文)"
echo "5. 尝试填入 M-ASYNC 并看Agda的反馈"

echo ""
echo "===== Next steps ====="
echo "如果M-ASYNC能成功proof，继续下一步："
echo "- example1-step2-valid (可能是S-SCHEDULE或直接到S-COMPLETE)"
echo "- example1-step3-valid (S-COMPLETE)"
echo "- example1-step4-valid (M-AWAIT)"

echo ""
echo "如果遇到问题："
echo "1. 检查OCaml trace和Agda configuration是否匹配"
echo "2. 检查规则的前提条件是否满足"
echo "3. 可能需要添加辅助lemma"
