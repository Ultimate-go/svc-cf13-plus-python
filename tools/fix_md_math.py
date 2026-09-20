"""把 Markdown 说明文档里的 LaTeX 数学换成 Unicode 纯文本。

背景：VS Code 自带的预览**不渲染** ``$...$`` / ``$$...$$``，所以文档里那些公式
在预览里是一堆反斜杠命令。本项目又不想为了看文档去装 Markdown+Math 扩展。

做法：把 ``$X$`` 换成 `` `X'` ``（内联代码），``$$X$$`` 换成围栏代码块，
其中 ``X'`` 是 ``X`` 的 LaTeX 命令被替换成对应 Unicode 符号后的结果。
风格与文档里本来就有的那种代码块（``g^{e_[n]/e_I}``）保持一致。

只处理代码围栏与已有反引号之外的区域。
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# LaTeX → Unicode
# ---------------------------------------------------------------------------

GREEK = {
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
    "varepsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "iota": "ι",
    "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π",
    "rho": "ρ", "sigma": "σ", "tau": "τ", "upsilon": "υ", "phi": "φ",
    "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω",
    "Gamma": "Γ", "Delta": "∆", "Theta": "Θ", "Lambda": "Λ", "Xi": "Ξ",
    "Pi": "Π", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω",
    "Upsilon": "Υ",
    "ell": "ℓ", "hbar": "ℏ", "imath": "ı", "jmath": "ȷ",
    "aleph": "ℵ", "Re": "ℜ", "Im": "ℑ",
}

SYMBOLS = {
    "prod": "∏", "sum": "Σ", "cdot": "·", "times": "×", "div": "÷",
    "notin": "∉", "in": "∈", "subseteq": "⊆", "subset": "⊂",
    "supseteq": "⊇", "supset": "⊃", "setminus": "∖", "cup": "∪", "cap": "∩",
    "varnothing": "∅", "emptyset": "∅", "forall": "∀", "exists": "∃",
    "to": "→", "rightarrow": "→", "leftarrow": "←", "gets": "←",
    "longleftarrow": "←", "longrightarrow": "→", "Rightarrow": "⇒",
    "Leftrightarrow": "⇔", "mapsto": "↦",
    "ge": "≥", "geq": "≥", "le": "≤", "leq": "≤", "ne": "≠", "neq": "≠",
    "approx": "≈", "equiv": "≡", "sim": "∼", "propto": "∝",
    "mid": "|", "lvert": "|", "rvert": "|", "vert": "|", "lVert": "‖",
    "rVert": "‖", "lfloor": "⌊", "rfloor": "⌋", "lceil": "⌈", "rceil": "⌉",
    "infty": "∞", "partial": "∂", "nabla": "∇",
    "wedge": "∧", "vee": "∨", "neg": "¬", "land": "∧", "lor": "∨",
    "oplus": "⊕", "otimes": "⊗", "dots": "…", "ldots": "…",
    "cdots": "⋯", "prime": "′", "bot": "⊥", "top": "⊤",
}

#: 直接删掉的排版命令
DROP = {
    "left", "right", "big", "Big", "bigl", "bigr", "Bigl", "Bigr",
    "qquad", "quad", "!", ",", ";", ":", " ",
}


def _strip_braces(s: str) -> str:
    """``{x}`` → ``x``（只在这一层确实没有嵌套命令时安全）。"""
    return s[1:-1]


def _find_group(s: str, start: int) -> tuple[str, int]:
    """从 ``start`` 处（应为 ``{``）取出配平的括号组，返回内容与结束位置。"""
    assert s[start] == "{"
    depth, i = 0, start
    while i < len(s):
        if s[i] == "{":
            depth += 1
        elif s[i] == "}":
            depth -= 1
            if depth == 0:
                return s[start + 1 : i], i + 1
        i += 1
    return s[start + 1 :], len(s)


def latex_to_unicode(src: str) -> str:
    """把一小段 LaTeX 公式转成可读的纯文本。"""
    out: list[str] = []
    i = 0
    while i < len(src):
        c = src[i]

        if c == "\\":
            # 反斜杠后面的命令名
            m = re.match(r"\\([A-Za-z]+|.)", src[i:])
            if not m:
                out.append(c)
                i += 1
                continue
            cmd = m.group(1)
            j = i + m.end()

            if cmd in DROP:
                i = j
                continue

            if cmd == "text" or cmd == "mathrm" or cmd == "mathsf" or cmd == "operatorname":
                if j < len(src) and src[j] == "{":
                    body, j = _find_group(src, j)
                    out.append(body)
                    i = j
                    continue

            if cmd == "frac":
                num, j = _find_group(src, j) if src[j] == "{" else ("", j)
                den, j = _find_group(src, j) if src[j] == "{" else ("", j)
                out.append(f"({latex_to_unicode(num)})/({latex_to_unicode(den)})")
                i = j
                continue

            if cmd == "sqrt":
                body, j = _find_group(src, j) if src[j] == "{" else ("", j)
                out.append(f"√({latex_to_unicode(body)})")
                i = j
                continue

            if cmd == "stackrel":
                top, j = _find_group(src, j) if src[j] == "{" else ("", j)
                rel, j = _find_group(src, j) if src[j] == "{" else ("", j)
                # \stackrel{?}{=} → ≟（“ questioned equal ”）
                out.append("≟" if top.strip() == "?" else f"{rel}")
                i = j
                continue

            if cmd == "mathbb":
                body, j = _find_group(src, j) if src[j] == "{" else ("", j)
                out.append({"Z": "ℤ", "N": "ℕ", "G": "𝔾"}.get(body, body))
                i = j
                continue

            if cmd == "mathcal" or cmd == "mathbf":
                body, j = _find_group(src, j) if src[j] == "{" else ("", j)
                out.append(body)
                i = j
                continue

            if cmd in GREEK:
                out.append(GREEK[cmd])
                i = j
                continue

            if cmd in SYMBOLS:
                out.append(SYMBOLS[cmd])
                i = j
                continue

            # 认不出来的命令：保留命令名，方便人工复查
            out.append(cmd)
            i = j
            continue

        if c in "^_":
            # ^{...} / _{...} 原样保留：文档里本来就有的代码块用的就是这种写法，
            # 改成括号反而与之不一致。
            out.append(c)
            i += 1
            continue

        out.append(c)
        i += 1

    text = "".join(out)
    text = re.sub(r"[ \t]{2,}", " ", text)
    text = re.sub(r"\s*\n\s*", " ", text)
    # | I | → |I|、·  两侧不留空格
    text = re.sub(r"\s*\|\s*", "|", text)
    text = re.sub(r"\s*·\s*", "·", text)
    # 集合运算符前后：只留一个空格在左侧，右侧不留
    text = re.sub(r"\s*([∖∪∩⊆⊂⊇⊃])\s*", r"\1", text)
    # 箭头两侧留一个空格（源文里 \leftarrow 后面常紧跟别的命令）
    text = re.sub(r"\s*←\s*", " ← ", text)
    text = re.sub(r"\s*→\s*", " → ", text)
    text = re.sub(r"[ \t]{2,}", " ", text)
    return text.strip()


# ---------------------------------------------------------------------------
# Markdown 层面
# ---------------------------------------------------------------------------

FENCE = re.compile(r"^(\s*)(```|~~~)")
INLINE_CODE = re.compile(r"`+[^`]*`+")


def convert_file(path: Path) -> tuple[int, int]:
    lines = path.read_text(encoding="utf-8").split("\n")
    out: list[str] = []
    in_fence = False
    n_block = n_inline = 0
    i = 0

    while i < len(lines):
        line = lines[i]

        if FENCE.match(line):
            in_fence = not in_fence
            out.append(line)
            i += 1
            continue

        if in_fence:
            out.append(line)
            i += 1
            continue

        # ---- $$ 块：可能独占一行，也可能与文字同行 ----
        if "$$" in line:
            head = line[: line.index("$$")]
            rest = line[line.index("$$") + 2 :]
            if "$$" in rest:
                body, tail = rest.split("$$", 1)
                out.append(head + "`" + latex_to_unicode(body) + "`" + tail)
                n_inline += 1
                i += 1
                continue
            # 跨行块：收集到出现闭合 $$ 的那一行为止
            body_lines = [rest]
            i += 1
            while i < len(lines) and "$$" not in lines[i]:
                body_lines.append(lines[i])
                i += 1
            tail = ""
            if i < len(lines):
                # 闭合行里 $$ 之前的那段也是公式的一部分，不能丢
                before, tail = lines[i].split("$$", 1)
                body_lines.append(before)
                i += 1
            body = latex_to_unicode(" ".join(body_lines))
            if head.strip():
                out.append(head.rstrip())
            out.append("```")
            out.append(body)
            out.append("```" + tail)
            n_block += 1
            continue

        # ---- 行内 $...$：逐个处理，跳过已有反引号 ----
        if "$" in line:
            pieces: list[str] = []
            pos = 0
            for code in INLINE_CODE.finditer(line):
                pieces.append(_inline_math(line[pos : code.start()]))
                pieces.append(code.group(0))
                pos = code.end()
            pieces.append(_inline_math(line[pos:]))
            new_line = "".join(pieces)
            n_inline += 0
            out.append(new_line)
            i += 1
            continue

        out.append(line)
        i += 1

    path.write_text("\n".join(out), encoding="utf-8")
    return n_block, n_inline


def _inline_math(seg: str) -> str:
    """把一段（不含代码span的）文本里的 ``$...$`` 换成内联代码。"""

    def repl(m: re.Match) -> str:
        return "`" + latex_to_unicode(m.group(1)) + "`"

    return re.sub(r"(?<!\$)\$(?!\$)([^$\n]+?)\$(?!\$)", repl, seg)


def main(argv: list[str]) -> int:
    targets = [Path(p) for p in argv[1:]]
    if not targets:
        targets = sorted(Path(".").rglob("*.md"))
    for p in targets:
        if ".pytest_cache" in p.parts:
            continue
        before = p.read_text(encoding="utf-8")
        if "$" not in before:
            print(f"  跳过 {p}（没有数学公式）")
            continue
        b, n = convert_file(p)
        after = p.read_text(encoding="utf-8")
        left = after.count("$")
        print(f"  {p}: 块公式 {b} 个，剩余 $ 数 {left}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
