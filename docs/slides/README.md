# Presentation Slides

This directory contains presentation materials for Sub_Async.

## Versions

### 1. SLIDES.md (Full Version)
**37 slides** — Complete presentation with detailed motivation and explanations.

**Audience:** General audience unfamiliar with async programming issues.

**Content:**
- Full motivation (OOP invocation, blocking, await problems)
- Chat group analogy
- Detailed case studies with step-by-step traces
- Trade-offs and open problems

**Generate PDF:**
```bash
pandoc SLIDES.md -t beamer -o pdf/slides.pdf \
  --slide-level=2 -V theme:metropolis -V aspectratio:169 \
  --highlight-style=tango --pdf-engine=xelatex
```

---

### 2. SLIDES_SHORT.md (Supervisor Version)
**~25 slides** — Problem-driven, concise presentation.

**Audience:** Supervisor familiar with the motivation.

**Content:**
- Three problems (OOP/Blocking/Await)
- Three decouplings (Space/Time/Coordination)
- Diamond case study with step-by-step trace
- Additional examples (Fire-and-Forget, Fibonacci)
- Trade-offs

**Generate PDF:**
```bash
pandoc SLIDES_SHORT.md -t beamer -o pdf/slides_short.pdf \
  --slide-level=2 -V theme:metropolis \
  --highlight-style=tango --pdf-engine=xelatex
```

---

### 3. SLIDES_CODE.md (Implementation Walkthrough)
**~22 slides** — Code-focused deep dive.

**Audience:** Technical audience wanting implementation details.

**Content:**
- Data structures (status types, global state, scheduler)
- Core algorithm (create, complete, await, resolve)
- Operator polymorphism implementation
- Diamond execution trace with code

**Generate PDF:**
```bash
pandoc SLIDES_CODE.md -t beamer -o pdf/slides_code.pdf \
  --slide-level=2 -V theme:metropolis -V aspectratio:169 \
  --highlight-style=tango --pdf-engine=xelatex
```

---

## Requirements

- **Pandoc** >= 2.0
- **XeLaTeX** (for Unicode support)
- **Metropolis Beamer theme**

Install on Ubuntu/Debian:
```bash
sudo apt install pandoc texlive-xetex texlive-fonts-extra
```

---

## Quick Build All

```bash
#!/bin/bash
cd "$(dirname "$0")"
pandoc SLIDES.md -t beamer -o pdf/slides.pdf --slide-level=2 -V theme:metropolis -V aspectratio:169 --highlight-style=tango --pdf-engine=xelatex
pandoc SLIDES_SHORT.md -t beamer -o pdf/slides_short.pdf --slide-level=2 -V theme:metropolis --highlight-style=tango --pdf-engine=xelatex
pandoc SLIDES_CODE.md -t beamer -o pdf/slides_code.pdf --slide-level=2 -V theme:metropolis -V aspectratio:169 --highlight-style=tango --pdf-engine=xelatex
```

---

## Note

PDFs are **not tracked in Git** (see `.gitignore`). Generate locally as needed.
