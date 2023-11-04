# wiki

- 使用 Logseq 文件版（Logseq OG，file graph）。
- 只给打算公开的那部分页面设置 `public:: true`。
- `Wiki Index` 作为 wiki 首页，需标记为 `public:: true` 并包含在导出中。

## 更新流程

1. 在 Logseq 中手动将公开页面（public pages）导出为 HTML 到此仓库。
2. 运行 `task prepare`，依次格式化嵌入数据、清洗数据库和配置，再设置首页并隐藏 `public` 属性。
3. 命令成功后，检查公开正文和附件，再提交本次改动。

需要保留前后对照时，运行 `task prepare -- --debug`。输出中的 `snapshot_dir` 指向 `/tmp` 下本次的私有目录，里面的 `original.html` 是刚读入的导出文件，`prepared.html` 是三个处理阶段全部完成后的结果。
