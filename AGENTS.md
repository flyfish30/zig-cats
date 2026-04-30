# AGENTS.md

本文件用于后续迭代时的协作约定，目标是让模型在本仓库中保持一致的术语、流程与工程边界。

## 本文件的使用方式（协作约定）

- 本文件是 **LLM 协作入口规范**：写代码、改文档、改 `build.zig` 前先对齐本文件约束。
- 任意术语改动（尤其是输入模式、测试分层、命令行参数）必须同步文档，避免同一概念多套命名。
- `docs/archive/` 视为**只读归档**，不做编辑。

## 项目目标（当前阶段）

- 使用Zig语言实现一个函数式编程的基础库，支持Functor, Applicative Functor, Monad, Lambda等。

## 工作流约定（compile/check)

当前仓库使用标准的zig build流程和测试流程。
build命令是：
zig build

test命令是：
zig build test


## 当前实现约束

- Zig 固定为 `0.16.0`。
- 必须使用 Zig `0.16.0` 对应的标准库与 build API。

## Zig 代码风格（0.16.0）

本仓库 Zig 代码（含 `build.zig`）以 `~/.cursor/skills-cursor/zig-0.16/SKILL.md` 为唯一权威规范。
Zig标准库的源代码请从Zig安装目录获取：`/opt/homebrew/Cellar/zig/0.16.0/lib/zig/std/`

### 通用风格

- 统一 `zig fmt`。
- 命名遵循现有代码风格与 Zig 标准库习惯。
- 错误处理使用 `!T` + `try/catch`，错误信息必须可操作。
- 变量命名避免无语义单字母缩写。
- 注释要求：**代码注释英文，设计文档中文**。
- 注释禁止包含里程碑编号（如 `M1.2`）。

## 文档风格要求

- docs 使用中文，并明确“设计动机 / 约束 / 不做什么 / 未来扩展点”。
- 文风使用设计文档口吻，避免对话式措辞。


## 常用命令（协作时直接用）

### 1) 格式化与基础测试

- `zig fmt .`
- `zig build test

### 2) 清理产物

- `rm -rf zig-out zig-cache gen`

