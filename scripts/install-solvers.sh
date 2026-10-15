#!/usr/bin/env bash
# =============================================================================
# scripts/install-solvers.sh — 安装 SMT 求解器到用户级目录
#
# 用途：为 `policylang` 准备 `ALG-3` 能力探测所需的三个后端。
# 安装位置（**不污染 PATH、不需要管理员权限**）：
#     ${HOME}/.local/share/policylang-solvers/<产品>/<版本>/bin/<exe>
# `policylang` 的可执行文件发现逻辑（`crates/policylang-solver/src/discover.rs`）
# 会递归搜索该目录，因此**无需修改 PATH**。
#
# 支持的覆盖方式：
#   POLICYLANG_SOLVER_PATH="/opt/solvers:/other/bin"   # 额外搜索根（; 或 : 分隔）
#   --solvers z3=/path/to/z3                            # 单次运行显式指定
#
# 用法：
#   bash scripts/install-solvers.sh            # 安装全部三个
#   bash scripts/install-solvers.sh z3 cvc5    # 只装指定后端
#   FORCE=1 bash scripts/install-solvers.sh    # 忽略已存在，强制重装
# =============================================================================
set -euo pipefail

ROOT="${POLICYLANG_SOLVER_HOME:-$HOME/.local/share/policylang-solvers}"
mkdir -p "$ROOT"

# 固定版本，保证可复现（升级时同步更新 `policylang.lock`）
Z3_VER="z3-5.3.0"
Z3_ASSET="z3-5.3.0-x64-win.zip"
CVC5_VER="cvc5-1.4.2"
CVC5_ASSET="cvc5-Win64-x86_64-static.zip"
BW_VER="0.9.1"
BW_ASSET="Bitwuzla-Win64-x86_64-static.zip"

want=("$@")
if [ ${#want[@]} -eq 0 ]; then want=(z3 cvc5 bitwuzla); fi

need() { # name
  for w in "${want[@]}"; do [ "$w" = "$1" ] && return 0; done
  return 1
}

install_one() { # name tag asset
  local name="$1" tag="$2" asset="$3"
  local dir="$ROOT/$name"
  local exe="$name.exe"
  command -v uname >/dev/null && case "$(uname -s)" in
    Linux) exe="$name";;
    Darwin) exe="$name";;
  esac

  if [ -z "${FORCE:-}" ] && find "$dir" -iname "$exe" -print -quit 2>/dev/null | grep -q .; then
    echo "[skip] $name 已存在（FORCE=1 可强制重装）"
    return 0
  fi

  local url="https://github.com/$4/releases/download/$tag/$asset"
  echo "[dl]   $name  <- $url"
  mkdir -p "$dir"
  curl -fL --retry 3 --retry-delay 3 --max-time 900 -sS -o "$dir/pkg.zip" "$url"

  echo "[unzip] $name"
  unzip -oq "$dir/pkg.zip" -d "$dir"
  rm -f "$dir/pkg.zip"

  local found
  found="$(find "$dir" -iname "$exe" -print -quit)"
  if [ -z "$found" ]; then echo "[FAIL] 未找到 $exe"; return 1; fi
  echo "[ok]   $name -> $found"
}

need z3       && install_one z3       "$Z3_VER"   "$Z3_ASSET"   Z3Prover/z3
need cvc5     && install_one cvc5     "$CVC5_VER" "$CVC5_ASSET" cvc5/cvc5
need bitwuzla && install_one bitwuzla "$BW_VER"   "$BW_ASSET"   bitwuzla/bitwuzla

echo
echo "安装根：$ROOT"
echo "已安装的可执行文件："
find "$ROOT" \( -iname 'z3.exe' -o -iname 'cvc5.exe' -o -iname 'bitwuzla.exe' \
              -o -iname 'z3' -o -iname 'cvc5' -o -iname 'bitwuzla' \) -type f 2>/dev/null | sort
echo
echo "验证：  policylang solvers"
echo "锁定：  policylang lock --write policylang.lock"
