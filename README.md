# toybox-lean4

Lean 4 を用いた形式検証をまとめたリポジトリです。

## コンテンツ

- [Prime avoidance](prime-avoidance/)
- [極大イデアルの冪による剰余環は局所環](quot-ring-mod-pow-of-max-ideal)

## メモ

- `cases (em p)`よりは`by_cases hp : p`の方が良さそう。
  後者だと`case pos => …`、`case neg => …`と続く。
- Coq でいう`repeat split`は`repeat' constructor` (`'`が付く)が近い。
