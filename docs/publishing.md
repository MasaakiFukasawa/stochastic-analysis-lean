# 公開内容と更新手順

公開先は [MasaakiFukasawa/stochastic-analysis-lean](https://github.com/MasaakiFukasawa/stochastic-analysis-lean) です。このフォルダがリポジトリのルートです。

公開するのはLeanソース、利用案内、依存関係の指定、検証結果です。教科書本文・TeX・PDF・非公開の照合記録は含めません。`.lake/` とログはGitの管理対象外です。`audit/latest-run.json` は公開対象で、検査を実行すると更新されます。

更新時は、次の順に確認します。

```sh
python3 scripts/audit.py --check-only
python3 scripts/audit.py
git diff --check
git status --short
git diff
```

証明ソースを変更すると、保存された検証済みハッシュとの不一致が検出されます。ビルド・公理監査・原稿対応の確認を行い、その結果に基づいて検証記録を更新してください。ハッシュの更新だけを検証成功として扱わないでください。

公開するファイルを確認して個別に `git add` し、コミットして `git push origin main` で反映します。元の原稿作業フォルダ全体は追加しません。

`lean-toolchain` と `lake-manifest.json` はコミット対象です。依存関係を変更するとき以外は `lake update` を実行しません。

GitHub Actionsの **Lean verification** は手動で起動できます。依存キャッシュを取得し、全体のビルドと公理監査を行います。実行結果はActionsの成果物に保存され、リポジトリ内の記録へは自動コミットされません。バージョンのタグは、ビルド・監査・原稿対応の確認を終えたコミットに付けてください。
