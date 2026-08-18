<!-- CLASSIFY: L0 -->
# vci-playground —— ci-playground 之公域 CI 影子引擎（SHADOW-CI-01 矩阵 · 演练承接）

**意图**：公域影子：特区演练（压测/攻击/磨合）的公域承接面——演练脚本、记录、战报公开归档

## 铁律
1. 本仓只载 L0/L1 公开面内容（CLASSIFY-01）；私域内容一律不走本仓。
2. 零密钥、零私仓凭证——本仓 Actions 只持 GITHUB_TOKEN（本仓 contents:write）。
3. 消费面 = 各线会话公开发布的 outbox/weave 件与 ci-control 公域注册表；产出 = weave/pulse/ 摘要与本仓提交史（即哈希链）。
4. 与 warm side（chepin-bi/ci-warm 私域镜像）并列常设：warm 管私域防灾，本仓管公域语义投影。

## 机制
- `shadow-pulse`：事件驱动（push engine/** · repository_dispatch · 手动），脉冲读取 ci-control/bridge/outboxes.json 注册表中对应对线 outbox，快照入 weave/pulse/ 并追加 pulse.log（自提交成链）。
- 引擎升级经 provision 车道（ci-control/provision/vci/vci-playground/）幂等下发。
