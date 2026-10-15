#!/usr/bin/env bash
#
# PolicyLang Meta — Lean 证明纪律门禁
# 对应规范：docs/12-Lean4形式化验证规范.md §12.7
#
# 作用：
#   1. 统计 Lean 工程中的 `sorry` 数量，并与里程碑预算比较；
#   2. 若超出预算则非零退出，阻断合并。
#
# 用法：
#   scripts/check-sorry.sh [目标目录] [预算]
#   SORRY_BUDGET=10 scripts/check-sorry.sh lean/PolicylangProof
#
# 里程碑预算（12 §12.6 的 burn-down 计划）：
#   M-2（阶段一末，G-4 验收）: 10
#   M-4（阶段二末）          : 4
#   M-6（阶段三末）          : 0
#
set -euo pipefail

TARGET_DIR="${1:-lean/PolicylangProof}"
BUDGET="${2:-${SORRY_BUDGET:-10}}"

if [ ! -d "$TARGET_DIR" ]; then
  echo "ERROR: 目录不存在: $TARGET_DIR" >&2
  exit 2
fi

# 统计 `sorry` / `admit` 出现次数（排除注释行以免误报）
COUNT=$(grep -rn --include='*.lean' -E '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' "$TARGET_DIR" \
        | grep -v -E '^\s*[^:]+:[0-9]+:\s*(--|/-)' \
        | wc -l | tr -d ' ')

echo "Lean sorry/admit count = ${COUNT} (budget = ${BUDGET})"

if [ "$COUNT" -gt "$BUDGET" ]; then
  echo "ERROR: sorry 数量 ${COUNT} 超出里程碑预算 ${BUDGET}" >&2
  echo "---- 超出位置 ----" >&2
  grep -rn --include='*.lean' -E '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' "$TARGET_DIR" \
    | grep -v -E '^\s*[^:]+:[0-9]+:\s*(--|/-)' >&2 || true
  exit 1
fi

echo "OK: Lean 证明纪律门禁通过"
exit 0
