# PHASE2_PLAN — 3 ladder-MR на новое ядро Yaffle (без отложки гэпов)

Worktree: `/Users/mikhailmurunov/models/idris2-yaffle-3754`
Ветка: `integrate/yaffle+ladder` (от `pr3754` = `26e69c7a4`, Yaffle new core).
Build env (всегда): `export PATH=/opt/homebrew/bin:$PATH CPATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib`
Сборка: `make SCHEME=chez` (idris2 self-build). idris2 ограничивает исходники CWD — запускать из папки файла.
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

- [ ] **G0 setup** — ветка `integrate/yaffle+ladder` создана (DONE при старте), файлы
  состояния закоммичены. Зафиксировать baseline: `make SCHEME=chez` нового ядра
  чист (если ещё не подтверждено в этой ветке — собрать), записать в журнал.

- [ ] **G1 #3779 DecEq reflection** — применить `gh pr diff 3779`, разрулить конфликт
  с Yaffle в `src/TTImp/Elab/RunElab.idr` + `libs/base/Language/Reflection.idr`,
  commit `[#3779] DecEq elaborator reflection on Yaffle core`.
  - Гейт: `make SCHEME=chez` чист; `make test only=idris2/reflection/reflection002` (+
    смежные reflection) зелёные; surface деривации DecEq (новый конструктор/hook в
    `Language.Reflection`) присутствует grep-проверяемо.

- [ ] **G2 #3737 type synonyms at derivings** — применить `gh pr diff 3737`, разрулить
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

- [ ] **G3 #3775 totality perf** — применить `gh pr diff 3775`, разрулить конфликт с
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
