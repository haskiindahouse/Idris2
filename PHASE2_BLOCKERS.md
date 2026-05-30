# PHASE2_BLOCKERS — только человеко-решаемые блокеры

Сюда писать ТОЛЬКО когда гэп реально требует решения человека (а не отложки).
Запись = повод для `<promise>PHASE2 BLOCKED: <one-line></promise>` и остановки.
Формат: дата, гэп (G1/G2/G3), точный файл/функция, что пробовал (команда/патч),
какой именно вопрос к человеку.

(пусто)

## 2026-05-30 — SCOPE DECISION NEEDED (Phase 2 endgame)
The 3 ladder MRs are fully integrated onto the Yaffle new core and the build is green:
- #3779 DecEq reflection (c7d0672c3): ported to Yaffle; 34/38 reflection tests pass.
- #3737 type synonyms at derivings (96f8951b9): clean apply; deriving+warning006 green;
  ALL review comments verified.
- #3775 totality perf (12a273da5): regression test total031 passes 1.82s; its CallGraph
  code change is subsumed by Yaffle's rewrite (tested+reverted, no measurable benefit).

BLOCKER (human decision, not a technical gap): the Yaffle DRAFT baseline itself has
PRE-EXISTING failing/slow tests in TARGET suites, independent of the 3 MRs:
- reflection: 002, 007 (hang ~130s), 008, 010 — Yaffle eval/quote/case repr + one real
  `Undefined {e:2}` core bug.
- totality: total029 FAIL (124s), total006 FAIL, total021 success-but-138s.
These fail because the Yaffle Value/eval/totality rewrite is still WIP (a draft PR), and
fixing them means fixing GulinSS's draft core — far outside "apply the 3 MRs".

QUESTION for the user:
(A) Accept Phase 2 as DONE = "3 MRs integrated onto Yaffle, build green, their own gates
    pass, zero NEW regressions" (pre-existing draft reds excluded, as the plan scoped); OR
(B) Expand scope to also fix the Yaffle draft's pre-existing reflection/totality failures
    (large, effectively co-developing the Yaffle core — weeks of work).
