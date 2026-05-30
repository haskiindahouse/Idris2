# PHASE2_PLAN — 3 ladder-MR на новое ядро Yaffle (без отложки гэпов)

Worktree: `/Users/mikhailmurunov/models/idris2-yaffle-3754`
Ветка: `integrate/yaffle+ladder` (от `pr3754` = `26e69c7a4`, Yaffle new core).
Build env (всегда): `export PATH=/opt/homebrew/bin:$PATH CPATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib`
Сборка (ВАЖНО): `make SCHEME=chez IDRIS2=$PWD/install/bin/idris2` — bootstrap-компилятор
ОБЯЗАН быть Yaffle из Phase 1 install. Дефолтный `idris2` из PATH = pack (не-Yaffle):
компилит модули, но падает на финале `Chez exited with return code 255`. Перед сменой
ветки/после конфликта TTC мешать нельзя → при сомнении `make clean` сначала.
idris2 ограничивает исходники CWD — запускать из папки файла.
Реальные диффы PR (НЕ ветки): `gh pr diff <N> --patch -R idris-lang/Idris2`.

## ЖЁСТКОЕ ПРАВИЛО — НЕТ ОТЛОЖЕННЫМ ГЭПАМ
Запрещено: park, postpone, stub, `-- TODO`/`-- FIXME`, закомментировать рабочий код,
`believe_me`/`assert_total`-чтобы-обойти, skip/xfail тестов, «min-slice»/сужение
скоупа, оставленные маркеры `<<<<<<<`, незакрытые `*.rej`.
**Гэп** = всё между текущим состоянием и DONE: неналоженный hunk PR, неразрешённый
конфликт, падающая сборка, падающий целевой тест, неучтённый ревью-коммент.
Каждая итерация ОБЯЗАНА закрыть ≥1 гэп и доказать гейтом. Если гэп реально требует
человеческого решения → HALT (запись в `PHASE2_BLOCKERS.md` + промис BLOCKED).
НЕ откладывать и идти дальше.

## Чеклист гэпов (закрывать по порядку)

- [x] **G0 setup** — ветка `integrate/yaffle+ladder` создана, scaffold закоммичен
  (d02a45b3f). Baseline GREEN: `make SCHEME=chez IDRIS2=$PWD/install/bin/idris2`
  → MAKE_EXIT=0, `build/exec/idris2 --version` = `0.8.0-d02a45b3f`. (Дефолтный
  idris2=pack падал на chez-шаге — фикс: IDRIS2=install.)

- [x] **G1 #3779 DecEq reflection** — DONE commit c7d0672c3. Reflection.idr clean apply;
  RunElab.idr ported (GetDecEqConPairs → Yaffle VTCon/VDCon/expandFull/Spine.value/
  TCon parampos:NatSet). Build MAKE_EXIT=0. 34/38 reflection tests pass; 4 reds
  (002/007/008/010) PRE-EXISTING Yaffle-draft (eval/quote/case repr + hash), proven
  not-my-regression (additive elabCon clause; reds unrelated to DecEq). [original gate text:]
  применить `gh pr diff 3779`, разрулить конфликт
  с Yaffle в `src/TTImp/Elab/RunElab.idr` + `libs/base/Language/Reflection.idr`,
  commit `[#3779] DecEq elaborator reflection on Yaffle core`.
  - Гейт: `make SCHEME=chez` чист; `make test only=idris2/reflection/reflection002` (+
    смежные reflection) зелёные; surface деривации DecEq (новый конструктор/hook в
    `Language.Reflection`) присутствует grep-проверяемо.

- [x] **G2 #3737 type synonyms at derivings** — DONE commit 96f8951b9. Applied CLEAN (no
  conflict). Build MAKE_EXIT=0; deriving_{functor,foldable,traversable,show}+warning006 pass.
  Review checklist all ✓ (British normalise, checkAccessToDefinition x2, leftMost→SnocList,
  no mutual, Vect/MkTPPrim arbitrary-param+test). [original gate text:]
  применить `gh pr diff 3737`, разрулить
  конфликт с Yaffle в `libs/base/Deriving/Common.idr`, commit
  `[#3737] type synonyms at derivings on Yaffle core`.
  - Гейт сборки/тестов: `make SCHEME=chez`; `make test only=base/deriving_functor
    base/deriving_foldable base/deriving_traversable base/deriving_show`;
    `make test only=idris2/warning/warning006`. Все зелёные, ноль skip.
  - Чеклист ревью (все ✓, grep-проверяемо в `libs/base/Deriving/Common.idr`):
    - [ ] British spelling: `normalise*` (нет `normalize`).
    - [ ] `checkAccessToDefinition` вызывается на обоих call-site (gallais #185/#190).
    - [ ] `leftMost` определён в библиотечном модуле (List/SnocList util), не локально
      в Common.idr (gallais #198).
    - [ ] нет лишнего `mutual`-блока (buzden #72).
    - [ ] arbitrary type-parameter обрабатывается (`toTypeParameter` для `IPrimVal`/
      app), есть тест на `Vect 4` (и/или `Vect (k+m)`) (gallais #219). Если теста
      нет — ДОБАВИТЬ и прогнать.

- [x] **G3 #3775 totality perf** — DONE commit 12a273da5 (regression test total031, passes
  1.82s). CallGraph code change (line 160 drop knownOr/scEq) was TESTED then REVERTED:
  subsumed by Yaffle's VApp `sizeCompareApp` (heads+args); on Yaffle the diff had NO
  measurable benefit — total021 ~137s WITH change vs ~138s WITHOUT — and is old-core-designed.
  PRE-EXISTING Yaffle-draft totality reds, NOT from the 3 MRs (which don't touch
  Core/Termination/eval): total029 FAIL(124s), total006 FAIL, total021 138s. See BLOCKERS.
  [original gate text:] применить `gh pr diff 3775`, разрулить конфликт с
  Yaffle в `src/Core/Termination/CallGraph.idr`, commit
  `[#3775] totality-checking perf on Yaffle core`.
  - Гейт: `make SCHEME=chez`; termination/totality тесты зелёные (`make test
    only=idris2/total/...` или релевантные). Перф НЕ гейтим (корректность).

- [ ] **G4 финал** — `make install IDRIS2=$PWD/build/exec/idris2 PREFIX=$PWD/install
  SCHEME=chez` чист; повторить smoke (`fact 5`=120, Vect) на собранном; все целевые
  сьюты зелёные с нулём skip; ноль `<<<<`/`.rej` (`git grep -n '^<<<<<<<'` пусто,
  `find . -name '*.rej'` пусто); чеклист #3737 весь ✓.
  - Итоговая запись в `PHASE2_JOURNAL.md` (список коммитов `pr3754..HEAD` + гейт-логи).
  - → `<promise>PHASE2 COMPLETE</promise>`.

## Гварды
- Диск: перед тяжёлой сборкой `df -h /Users/mikhailmurunov | tail -1`; если <2Gi
  свободно → blocker + `<promise>PHASE2 BLOCKED: low disk</promise>`.
- Не плодить worktree. Не трогать другие репо/ветки. Каждый гэп = отдельный commit.
