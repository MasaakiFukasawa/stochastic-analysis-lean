# GitHubへの公開

この `stochastic-analysis-lean` フォルダを新しいGitリポジトリのルートにしてください。

```sh
python3 scripts/audit.py --check-only
git init
git add .
git commit -m "Publish manuscript proof files and reproducible Lean project"
```

GitHubで空のリポジトリを作成し、その画面に表示されるリモートURLを `origin` に登録してpushします。`.gitignore` によって `.lake/`・ログ・実行時の監査結果は除外されます。原稿PDF・TeXや元の作業フォルダ全体を追加する必要はありません。

`lean-toolchain` と `lake-manifest.json` はコミット対象です。依存関係を更新する目的がなければ `lake update` で別のMathlibへ切り替えないでください。

公開後はGitHub Actionsの **Lean verification** を手動実行できます。Mathlibのキャッシュを取得し、全体のビルドと公理監査を行います。全章ビルドには時間がかかるため、標準では手動起動にしています。

バージョンを付ける際は、Leanのビルド成功、監査成功、原稿対応表の確認を記録したコミットにタグを付けると、他の人が同じ版を利用できます。
