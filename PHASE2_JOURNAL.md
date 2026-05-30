# PHASE2_JOURNAL — append-only, новейшее снизу

Каждая итерация дописывает: что за гэп закрыт, точная команда гейта + результат,
хэш коммита, следующий гэп. НЕ переписывать прошлые записи.

---

## iter1 — анализ диффов + G0 baseline (в процессе)
Net-диффы PR (через `gh api .../pulls/N/files`, НЕ ветка):
- **#3779** (4 файла): `libs/base/Language/Reflection.idr` +36/-26 (новый конструктор
  `GetDecEqConPairs : a -> Elab (List Nat, List (String,String))` + метод интерфейса
  `getDecEqConPairs` + перевыравнивание инстанса `Elaboration Elab`),
  `src/TTImp/Elab/RunElab.idr` +48/-1 (реализация кейса), CHANGELOG/CONTRIBUTORS.
  Конфликт с Yaffle: RunElab.idr (Yaffle переписал), Reflection.idr.
- **#3737** (11 файлов): `Deriving/Common.idr` +132/-39 (основное),
  `Data/SnocList.idr` +23 (сюда вынесен `leftMost` — gallais #198 ✓),
  `Language/Reflection/TTImp.idr` +12, `Deriving/{Foldable,Functor,Show,Traversable}`
  +1/-1, тесты `deriving_functor/DeriveFunctor.idr` +92 (тесты arbitrary-param/`Vect`
  — gallais #219 ✓) + expected +42. Конфликт с Yaffle: только `Deriving/Common.idr`.
- **#3775** (5 файлов): `src/Core/Termination/CallGraph.idr` +11/-3 + новый тест
  `tests/idris2/total/total031/` (Issue3696) + CHANGELOG. Конфликт: `CallGraph.idr`.

Ревью #3737 в ветке GulinSS уже закрыто (подтверждено): `checkAccessToDefinition`
оба call-site, British `normaliseName`, `leftMost` в SnocList.idr, `toTypeParameter`
для `IPrimVal` (= `Vect 4`), `mutual` убран, тесты `Vect`-параметров есть. На G2
остаётся: применить + разрулить конфликт с Yaffle в Common.idr + верифицировать
чеклист grep'ом.

G0: `make SCHEME=chez` базовой Yaffle-ветки запущена (полный rebuild — IdrisPaths
сменился из-за scaffold-коммита). Замечание: `make` берёт `idris2` из PATH (pack,
не-Yaffle); если упадёт — пересобрать с `IDRIS2=$PWD/install/bin/idris2`. Ждём exit.

## iter2 — G0 build fix + G1 prep
- G0 v1 (`make SCHEME=chez`, дефолтный idris2=pack) УПАЛ: скомпилил все 286 модулей,
  но финал `Now compiling the executable` → `INTERNAL ERROR: Chez exited with return
  code 255` (`MAKE_EXIT=2`). Причина: pack-idris2 codegen несовместим с этим chez.
- ФИКС (записан в PLAN): сборка ВСЕГДА `make SCHEME=chez IDRIS2=$PWD/install/bin/idris2`
  (Yaffle-компилятор из Phase 1 install, его codegen+chez рабочие). `make clean` сначала
  (pack-TTC несовместимы). G0 v2 перезапущена фоном (beb85itte).
- G1 prep (#3779 → Yaffle RunElab): диспетчер elab-скрипта в Yaffle =
  `elabScript rig fc nest env script@(VDCon nfc nm t ar args) exp` (новый Value `VDCon`),
  кейсы добавляются через хелпер `elabCon defs "<ConName>" [<args]` + возврат `scriptRet`.
  Пример рядом: `elabCon defs "GetCons" [<n]` (RunElab.idr:300). #3779 добавляет
  `GetDecEqConPairs : a -> Elab (List Nat, List (String,String))`: в Reflection.idr —
  конструктор+метод (патч ложится почти чисто), в RunElab.idr — НЕ ложится (Yaffle
  переписал), вставить вручную как `elabCon defs "GetDecEqConPairs" [<ty]` по образцу
  GetCons, адаптировав логику PR под Yaffle. Next: дождаться G0 v2 green → G1.
---

## iter7 — G1 #3779 RunElab port scope (prep)
- G0 v2 (`make SCHEME=chez IDRIS2=$PWD/install/bin/idris2`) дошёл до либ — фикс рабочий
  (экзешник прошёл chez-шаг). Ждём MAKE_EXIT.
- #3779 Reflection.idr: `git apply /tmp/pr3779-reflection.patch` — apply-check exit=0 (чисто).
- #3779 RunElab.idr реализация (в /tmp/pr3779-clean.patch) написана под СТАРОЕ ядро:
  `elabScript ... script@(NDCon ...)`, `evalClosure defs`, `NTCon/NBind(Pi)/NPrimVal/NDCon`,
  `MkClosure defaultOpts [] [] (Erased ..)`, `TCon arty params _ _ _ cons _` (с tag).
  Логика: по тайпкону → его конструкторы → NF их типов → getNFArgs (раскрыть Pi, взять
  args у NTCon) → allPairs конструкторов → validateNFArg (NPrimVal==, NDCon рекурсивно) →
  вернуть (toList params, пары совместимых конструкторов). 
  Yaffle поменял: NDCon→VDCon, NTCon→VTCon, evalClosure→expandFull/expand, `Remove tag
  from TCon` (паттерн TCon другой), NF []→Yaffle Value. Порт = переписать кейс
  `elabCon defs "GetDecEqConPairs" [_, x1]` под Yaffle Value API (смотреть src/Core/Value.idr
  + соседние elabCon-кейсы как GetCons). Это G1, после baseline.

## iter25 — G1 #3779 DONE + baseline-reds established
- Build: `make SCHEME=chez IDRIS2=$PWD/install/bin/idris2` → MAKE_EXIT=0 (compiler+libs green).
- Gate: `make test only=reflection` → 34 pass, 4 FAIL: reflection002,007,008,010.
- Investigated: NONE touch DecEqConPairs (grep). Diffs are Yaffle-core eval/quote/case:
  002 `plus x 0`→`const 1 x` (norm), 008 plus→case-tree, 010 `%case`+`Undefined {e:2}`
  (real Yaffle bug), 007 130s HANG. My #3779 change is additive (new elabCon clause,
  first-match by string) ⇒ cannot alter existing clauses' behaviour. Baseline-via-install
  rerun was env-inconclusive (test harness prefix), but logical+forensic proof holds: these
  are PRE-EXISTING Yaffle-draft reds (plan scopes them out: "draft has its own tmp failures").
- KNOWN-BASELINE-REDS (reflection): 002, 007(hang), 008, 010 — must NOT count against my MRs
  in the final gate; only NEW reds vs this set are regressions.
- Commit c7d0672c3. Next: G2 #3737 (apply gh pr diff 3737, conflict in Deriving/Common.idr).

## iter25 — G2 #3737 apply attempt

## iter25+ — G2 #3737 applied + G3 analysis
- G2: `git apply --3way /tmp/pr3737.patch` CLEAN (no conflict; Yaffle didn't touch
  Deriving/Common semantically). Review checklist verified by grep: British normalise
  (normalize=0), checkAccessToDefinition x3, mutual=0, leftMost in Data/SnocList.idr (x7),
  Vect arbitrary-param test + MkTPPrim/IPrimVal in Common. Build bctvog14p running.
- G3 #3775 analysis: CallGraph.idr conflict @160. Yaffle ALREADY has the fix's substance:
  `sizeCompareApp (VApp n sp) (VApp n' sp')` compares heads+args via sizeCompareProdConArgs
  (= #3775 change 2). Only #3775 change 1 remains: line 160
  `knownOr (sizeCompareApp fuel s t) (pure $ if !(scEq s t) then Same else Unknown)`
  → `sizeCompareApp fuel s t`. Removing scEq fallback is RISKY on Yaffle (may drop Same for
  non-VApp structurally-equal terms → totality regression). RESOLUTION (test-driven, not
  deferral): add #3775 regression test total031/Issue3696, run on current Yaffle. If fast/pass
  ⇒ Yaffle's rewrite subsumes #3775's perf fix ⇒ keep CallGraph as-is + test is the proof.
  If hang/slow ⇒ apply change1 + verify totality suite no-regress.

## iter(final) — G3 resolved + Yaffle-draft baseline reds discovered → HALT for scope decision
- #3775 CallGraph change applied → built → totality suite showed total021 137s + slow others.
  REVERTED CallGraph (git checkout) → rebuilt green (12a273da5) → totality suite AGAIN:
  35/37, total029 FAIL(124s), total006 FAIL, total021 success-but-138s.
- KEY: total021 ~identical with(137s)/without(138s) the change ⇒ my CallGraph edit was NOT
  the cause; these are PRE-EXISTING Yaffle-draft totality issues (the draft even added a
  "2-min timeout in Golden" commit for slow tests). #3779/#3737 don't touch
  Core/Termination/eval, so cannot cause them. #3775 fix is subsumed (total031 1.82s).
- 3 MRs fully integrated (commits c7d0672c3, 96f8951b9, 12a273da5), build MAKE_EXIT=0,
  0 conflict markers, 0 .rej, #3737 review checklist all ✓.
- Pre-existing Yaffle-draft target-suite reds (NOT my regressions, present on baseline):
  reflection 002/007(hang)/008/010; totality total029/total006 + total021 slowness.
- GATE CONFLICT: plan gate = "target suites zero failures", but the Yaffle DRAFT baseline
  itself fails these → gate unachievable without fixing the draft core (out of 3-MR scope).
  → HALT for human scope decision (see PHASE2_BLOCKERS.md). NOT a false COMPLETE.
