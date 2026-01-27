# Sub_Async Formalization

This directory contains the formal verification of Sub_Async's operational semantics and type system in Agda.

## Directory Structure

```
formalization/
├── learning/          # Agda tutorials and learning exercises
│   └── *.agda        # Practice files from PLFA, Agda docs, etc.
├── agda/             # Formal proof of Sub_Async Core Calculus
│   ├── Syntax.agda          # AST definitions
│   ├── Semantics.agda       # Small-step operational semantics
│   ├── TypeSystem.agda      # Typing rules
│   ├── Progress.agda        # Progress theorem
│   ├── Preservation.agda    # Preservation theorem
│   └── FutureResolution.agda # Future resolution property
└── README.md         # This file
```

## Getting Started with Agda

### Installation

**Official Guides**:
- Agda: https://agda.readthedocs.io/en/latest/getting-started/installation.html
- PLFA-zh: https://github.com/Agda-zh/PLFA-zh (推荐参考这个！)

**Recommended: Install via Cabal (PLFA-zh 推荐方式)**

PLFA 使用 Agda 2.7.0。按以下步骤安装：

**Step 1: 安装 GHC 和 Cabal**
```bash
# 使用 ghcup 安装 (推荐)
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

# 安装指定版本
ghcup install ghc 9.4.8
ghcup install cabal recommended

ghcup set ghc 9.4.8
ghcup set cabal recommended

# 或使用 ghcup tui 交互式设置
```

**Step 2: 安装 Agda**
```bash
cabal update
cabal install Agda-2.7.0

# 这一步会消耗较长时间和较多内存
# 完成后确认安装
agda --version
```

**Step 3: 配置 Agda mode (Emacs 或 VSCode)**
```bash
# Emacs 用户
agda-mode setup
agda-mode compile

# VSCode 用户
# 安装扩展: banacorn.agda-mode
# 在 settings.json 中指定 agda 路径
```

**Step 4: 安装 Agda 标准库**
```bash
# Clone 标准库
git clone https://github.com/agda/agda-stdlib.git ~/.agda/agda-stdlib

# 配置库路径
mkdir -p ~/.agda
echo "~/.agda/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries
echo "standard-library" >> ~/.agda/defaults
```

**Alternative: Quick Install (可能版本旧)**
```bash
# 包管理器方式 (Ubuntu/Debian)
sudo apt install agda
agda --version  # 检查版本是否符合要求

# 或从 GitHub 下载预编译二进制
# https://github.com/agda/agda/releases/
```

### Learning Resources

1. **Start here**: [PLFA (Programming Language Foundations in Agda)](https://plfa.github.io/)
   - Part 1: Logical Foundations (Naturals, Induction, Relations)
   - Part 2: Programming Language Foundations (Lambda calculus, Properties, DeBruijn)

2. **Official Tutorial**: [Agda Tutorial](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html)

3. **Reference Projects**:
   - `../external_resources/aeff-formalization/` - Aeff's Agda proofs (study Progress/Preservation structure)

### Workflow

**Phase 1: Learn Agda Basics** (Week 5)
```bash
cd formalization/learning
# Create practice files following PLFA chapters
# - Naturals.agda
# - Relations.agda
# - Lambda.agda
```

**Phase 2: Formalize Sub_Async** (Week 6-8)
```bash
cd formalization/agda
# Start with syntax, then semantics, then proofs
agda --safe Syntax.agda
agda --safe Semantics.agda
# ... iteratively build and type-check
```

### Type-Checking Commands

```bash
# Check a file
agda Syntax.agda

# Safe mode (no postulates, unsafe features)
agda --safe Syntax.agda

# Interactive mode in Emacs/VSCode
# C-c C-l  : Load file
# C-c C-c  : Case split
# C-c C-r  : Refine hole
# C-c C-a  : Auto proof search
```

## Current Status

- [ ] Phase 1: Learn Agda basics (PLFA Part 1)
- [ ] Phase 2: Define Core Calculus syntax
- [ ] Phase 3: Define small-step semantics
- [ ] Phase 4: Define type system
- [ ] Phase 5: Prove Progress
- [ ] Phase 6: Prove Preservation
- [ ] Phase 7: Prove Future Resolution

## Reference: Core Calculus Design

Based on `docs/ROADMAP.md`, our target calculus:

**Syntax:**
```
V ::= n | x | fut_id
e ::= V | e₁ ⊕ e₂ | async e | let x = e₁ in e₂
```

**Configuration:**
```
Σ = ⟨e, ρ, Φ, Q⟩
  e — Current expression
  ρ — Environment (x → V)
  Φ — Future table (fut_id → FutureStatus)
  Q — Task queue
```

**Small-Step Rules:** See `docs/ROADMAP.md` for draft rules.

## Notes

- **Keep it simple**: Start with Core Calculus (no booleans, no functions initially)
- **Study Aeff first**: Their formalization in `external_resources/aeff-formalization/` provides patterns
- **Iterate**: Don't try to formalize everything at once; build incrementally
