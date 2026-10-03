# 確率解析とその応用 — Lean 4 証明ファイル

本文第1–13章と付録の証明を点検するために作成したLeanコードです。章ごとの入口から定理を読み込み、自分の証明でも利用できます。

**検証するのはLeanに記述された命題です。** 原稿との対応は別途点検しています。原稿の日本語をLeanが自動的に検査するものではなく、各定理に明記された仮定は利用時にも必要です。[検証範囲](docs/coverage.md)を参照してください。

## 最初の実行

[elan](https://github.com/leanprover/elan) と Python 3 を用意し、このフォルダで実行します。Leanのバージョンは `lean-toolchain` により選ばれます。

```sh
lake exe cache get
lake build
python3 scripts/audit.py --skip-build
```

初回はMathlibとそのビルドキャッシュを取得するためネット接続が必要です。以後は変更したモジュールとその依存先だけをLakeが再ビルドします。全章の初回ビルドには時間とメモリが必要です。

第13章だけを読みたい場合は、次のように対象を指定できます。

```sh
lake build +Book.Chapter13
```

Leanファイルでは次のように利用します。

```lean
import Book.Chapter13

#check Asakura.Chapter13.closed_bond_pricing_martingale
#check Asakura.Chapter13.numeraire_payoff_pricing
```

全体は `import Book`、付録は `import Book.Appendices` です。元の確率過程から構成と結論をつなぐ定理は `import Book.Constructed` からも読み込めます。他のプロジェクトからは、このリポジトリをLakeの依存パッケージに指定します。LeanとMathlibのバージョンも合わせてください。

## 章を選ぶ

[章別の案内](docs/chapters.md)には、各章の入口、証明ファイル、原稿との対応表へのリンクがあります。

| フォルダ・ファイル | 内容 |
|---|---|
| `src/Book/Chapter01.lean` ～ `Chapter13.lean` | 章別の入口 |
| `src/Book/Appendices.lean` | 付録の入口 |
| `src/*.lean` | 証明本体 |
| `docs/chapters/` | 章別の利用案内 |
| `audit/chapters/` | 原稿とLean命題の対応表・検証結果 |
| `audit/constructed-interfaces.json` | 構成から結論までをつなぐ定理と検証結果 |
| `audit/verified-snapshot.json` | 検証済みソースのハッシュと定理一覧 |
| `scripts/audit.py` | ビルド・公理依存の再検査 |

章を選ぶ際は **`Book.ChapterXX` と案内表** を使ってください。複数の章で共有する補題は同じ証明ファイルから読み込みます。

## 固定した環境

- Lean: `leanprover/lean4:v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- 依存パッケージ: `lake-manifest.json` で固定
- 許す公理: `propext`, `Classical.choice`, `Quot.sound`

検証済みファイルの一致だけを調べるには `python3 scripts/audit.py --check-only` を使います。これはLeanの再コンパイルではありません。証明を編集した場合は、ハッシュを更新するだけで検証済みとせず、ビルド・公理監査・原稿対応の確認をやり直してください。

## 公開とライセンス

公開先は [MasaakiFukasawa/stochastic-analysis-lean](https://github.com/MasaakiFukasawa/stochastic-analysis-lean) です。[公開内容と更新手順](docs/publishing.md)を参照してください。原稿本文・TeX・PDFと組版用クラスファイルは含めていません。対応表には命題の識別情報とLeanの参照先を記載し、本文の転載は含めません。

既存コードのApache License 2.0とMathlib由来の著作権表示を保持しています。[LICENSE](LICENSE)・[NOTICE](NOTICE)を参照してください。
