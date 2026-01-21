# Advanced Documentation

This directory contains detailed technical documentation for advanced topics.

## Contents

- **SLIDES.md** - Presentation slides (Pandoc Beamer format)
- **DESIGN_DECISIONS.md** - Design trade-offs and rationale (short-circuit evaluation, GC, CPS, etc.)
- **PATTERNS_EXPLAINED.md** - Common async patterns and examples
- **IMPLEMENTATION.md** (TODO) - Implementation details, code structure, and internal APIs
- **THEORY.md** (TODO) - Theoretical foundations (DAG properties, type system proofs)
- **EXTENDING.md** (TODO) - Guide for extending the language with new features

---

## Building Slides

```bash
# Generate PDF slides with Beamer
pandoc docs/SLIDES.md -t beamer -o slides.pdf \
  --slide-level=2 \
  -V theme:metropolis \
  -V aspectratio:169 \
  --highlight-style=tango

# Or HTML slides with reveal.js
pandoc docs/SLIDES.md -t revealjs -o slides.html \
  -s --slide-level=2
```

---

For quick start and user-facing documentation, see the main [README.md](../README.md).
