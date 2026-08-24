#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mc-convergence: 蒙特卡洛收敛宪章验证 + 链种子可审计随机性 + NW toy PRG
公域 L0 内容: 纯 Python+numpy, CPU, 无外网依赖, 无密钥/个人标识。

Part A  臂流引擎仿真(收敛宪章):
  - 到达: 每 epoch N ~ Poisson(lam) 个臂
  - 单臂预算: beta ~ Exp(mean=beta_bar)
  - 引擎: 每 epoch 总算力 B, 门禁 K_max (至多 K_max 臂并行, 先到先服务, 均分 B)
  - 早停: 残余需求 <= eps 即停机
  - 负载率 rho = lam * beta_bar / B
  组1 rho<1 (门禁): 期望池长有界、全臂停机、遗憾斜率 ~ 0
  组2 rho<1 近临界 (门禁): 同上但更接近临界
  组3 rho>=1 无门禁 (对照): 期望池长/遗憾线性爆炸
  200 epoch x 50 重复, 各组输出池长分布/停机率/遗憾斜率。

Part B  链种子 PRNG + NW toy:
  - seed = sha256("usrm-outbox chain tip 占位串") -> default_rng -> 同一调度序列两次完全一致
  - NW toy: f=parity (平均难), (l,a)=(4,1) 目标组合设计, 8 比特种子 -> 32 比特伪随机串
    注: d=8,l=4 上严格 a<=1 设计至多 m=4 组 (C(8,2)/C(4,2)=28/6), 故贪心构造
        在交集预算内尽力扩展并如实报告达成参数 (NW 混合论证对交集退化平滑)。
  - 自相关检查: 全部 256 个种子输出级联成 8192 比特流, 滞后 1..16 归一化自相关 ~ 0

Part C  全部结果写 /kaggle/working/out.json (本地运行时落当前目录)。
"""
import hashlib
import json
import math
import os
from itertools import combinations

import numpy as np

EPOCHS = 200
REPEATS = 50
MASTER_SEED = 20260824


# ---------------- Part A: 臂流引擎 ----------------
def run_engine(lam, beta_bar, B, eps, k_max, epochs, rng):
    """单轮仿真: 返回逐 epoch 池长与残余需求(遗憾代理)序列及计数。"""
    pool = []  # 各臂残余需求
    arrived = 0
    stopped = 0
    pool_series = np.empty(epochs, dtype=np.float64)
    resid_series = np.empty(epochs, dtype=np.float64)
    for t in range(epochs):
        for _ in range(rng.poisson(lam)):
            pool.append(float(rng.exponential(beta_bar)))
            arrived += 1
        k = len(pool) if k_max is None else min(k_max, len(pool))
        if k > 0:
            share = B / k
            survivors = []
            for i, r in enumerate(pool):
                if i < k:
                    r -= share
                    if r <= eps:  # 早停: 残余 <= eps 视为收敛停机
                        stopped += 1
                        continue
                survivors.append(r)
            pool = survivors
        pool_series[t] = len(pool)
        resid_series[t] = float(np.sum(pool)) if pool else 0.0
    return {
        "arrived": arrived,
        "stopped": stopped,
        "pool_series": pool_series,
        "resid_series": resid_series,
    }


def ols_slope(y):
    """最小二乘斜率 (y vs t)。"""
    t = np.arange(len(y), dtype=np.float64)
    t_c = t - t.mean()
    return float(np.dot(t_c, y) / np.dot(t_c, t_c))


def run_group(name, lam, beta_bar, B, eps, k_max, master_ss):
    rho = lam * beta_bar / B
    seqs = master_ss.spawn(REPEATS)
    pool_all = []
    stop_rates = []
    regret_slopes = []
    final_pools = []
    for rep in range(REPEATS):
        rng = np.random.default_rng(seqs[rep])
        res = run_engine(lam, beta_bar, B, eps, k_max, EPOCHS, rng)
        pool_all.append(res["pool_series"])
        stop_rates.append(res["stopped"] / max(1, res["arrived"]))
        regret_slopes.append(ols_slope(res["resid_series"]))
        final_pools.append(res["pool_series"][-1])
    pool_flat = np.concatenate(pool_all)
    q = np.percentile(pool_flat, [50, 90, 99])
    return {
        "name": name,
        "params": {
            "lambda": lam, "beta_bar": beta_bar, "B": B, "eps": eps,
            "K_max": k_max if k_max is not None else "none(无门禁)",
            "rho": round(rho, 4), "epochs": EPOCHS, "repeats": REPEATS,
        },
        "pool_len": {
            "mean": round(float(pool_flat.mean()), 3),
            "p50": round(float(q[0]), 3),
            "p90": round(float(q[1]), 3),
            "p99": round(float(q[2]), 3),
            "max": int(pool_flat.max()),
            "final_mean": round(float(np.mean(final_pools)), 3),
        },
        "stop_rate": {
            "mean": round(float(np.mean(stop_rates)), 4),
            "min": round(float(np.min(stop_rates)), 4),
        },
        "regret_slope": {
            "mean": round(float(np.mean(regret_slopes)), 4),
            "sd": round(float(np.std(regret_slopes)), 4),
        },
        "verdict": None,  # 汇总阶段填
    }


def part_a():
    ss = np.random.SeedSequence(MASTER_SEED)
    gss = ss.spawn(3)
    groups = [
        run_group("rho_sub_gated",    2.0, 10.0, 30.0, 0.5, 32,    gss[0]),  # rho=0.667
        run_group("rho_near1_gated",  3.0, 10.0, 33.0, 0.5, 64,    gss[1]),  # rho=0.909
        run_group("rho_super_control", 4.0, 12.0, 40.0, 0.5, None, gss[2]),  # rho=1.2 无门禁对照
    ]
    for g in groups:
        rho = g["params"]["rho"]
        slope = g["regret_slope"]["mean"]
        stop = g["stop_rate"]["mean"]
        if rho < 1:
            ok = (stop >= 0.95) and (abs(slope) < 1.0)
            g["verdict"] = "bounded+stopped" if ok else "UNEXPECTED"
        else:
            ok = (slope > 1.0) and (g["pool_len"]["final_mean"] > 100)
            g["verdict"] = "explosion(control)" if ok else "UNEXPECTED"
    return groups


# ---------------- Part B: 链种子 PRNG + NW toy ----------------
CHAIN_TIP = "usrm-outbox chain tip 占位串"


def make_schedule(seed, n_arms=8):
    """由种子生成一轮臂调度序列(顺序+配额)。"""
    rng = np.random.default_rng(seed)
    return {
        "order": [int(x) for x in rng.permutation(n_arms)],
        "quotas": [int(x) for x in rng.integers(1, 9, size=n_arms)],
    }


def parity(bits):
    return int(sum(bits) % 2)


def build_design(d, l, a_target, m, seed):
    """贪心构造 NW 组合设计: d 点宇宙, 组大小 l, 目标两两交集 <= a_target, 目标 m 组。
    严格预算下组数不足时逐步放宽交集预算, 如实报告达成值。"""
    rng = np.random.default_rng(seed)
    cands = [list(c) for c in combinations(range(d), l)]
    order = rng.permutation(len(cands))
    cands = [cands[i] for i in order]
    for a in range(a_target, l):
        sets = []
        for c in cands:
            if all(len(set(c) & set(s)) <= a for s in sets):
                sets.append(c)
                if len(sets) == m:
                    break
        if len(sets) == m:
            return sets, a
    return sets, a  # 尽力而为(本参数下不会发生)


def nw_expand(x, sets, d):
    """NW 生成器: G(x)_i = parity(x|_{S_i})。"""
    bits = [(x >> (d - 1 - j)) & 1 for j in range(d)]
    return [parity([bits[j] for j in s]) for s in sets]


def part_b():
    digest = hashlib.sha256(CHAIN_TIP.encode("utf-8")).digest()
    chain_seed = int.from_bytes(digest[:8], "big")

    # 可复现随机性: 同一种子两次生成完全一致的调度序列
    s1 = make_schedule(chain_seed)
    s2 = make_schedule(chain_seed)
    repro_identical = (s1 == s2)
    sched_hash = hashlib.sha256(
        json.dumps(s1, sort_keys=True).encode("utf-8")).hexdigest()

    # NW toy: (l,a)=(4,1) 目标设计, 8 比特 -> 32 比特
    d, l, a_target, m = 8, 4, 1, 32
    sets, a_achieved = build_design(d, l, a_target, m, chain_seed ^ 0x9E3779B9)
    inter = [len(set(sets[i]) & set(sets[j]))
             for i in range(len(sets)) for j in range(i + 1, len(sets))]
    demo_seed_byte = digest[8]
    pr_bits = nw_expand(demo_seed_byte, sets, d)
    pr_hex = int("".join(map(str, pr_bits)), 2) if pr_bits else 0
    pr_hex_str = format(pr_bits and int("".join(map(str, pr_bits)), 2) or 0, "08x")

    # 自相关检查: 级联全部 256 个种子的 32 比特输出 -> 8192 比特 ±1 流
    stream = []
    for x in range(1 << d):
        stream.extend(1 if b else -1 for b in nw_expand(x, sets, d))
    arr = np.array(stream, dtype=np.float64)
    balance = float(arr.mean())
    autocorr = {}
    for lag in range(1, 17):
        autocorr[str(lag)] = round(float(np.mean(arr[:-lag] * arr[lag:])), 5)

    return {
        "chain_tip_material": CHAIN_TIP,
        "chain_seed_hex": format(chain_seed, "016x"),
        "schedule_repro": {
            "identical": repro_identical,
            "schedule_sha256": sched_hash,
            "schedule": s1,
        },
        "nw_toy": {
            "hard_function": "parity",
            "design": {
                "d": d, "l": l, "a_target": a_target, "m": m,
                "a_achieved": a_achieved,
                "max_intersection": int(max(inter)),
                "mean_intersection": round(float(np.mean(inter)), 4),
                "note": "d=8,l=4: 严格 a<=1 至多 m=C(8,2)/C(4,2)=4 组; a<=2 至多 14 组 "
                        "(常重码 A(8,4,4)=14); 故 m=32 时 max 交集 3 已为数学下界, "
                        "贪心构造达成该下界并如实报告",
            },
            "expansion": "8bit -> 32bit (4x)",
            "demo_seed_byte_hex": format(demo_seed_byte, "02x"),
            "pr_output_hex": pr_hex_str,
            "pr_output_bits": "".join(map(str, pr_bits)),
            "balance_mean_pm1": round(balance, 5),
            "autocorr_lag1_16": autocorr,
        },
    }


def main():
    out = {
        "kernel": "mc-convergence",
        "spec": "mc-convergence-charter/v1",
        "epochs": EPOCHS,
        "repeats": REPEATS,
        "part_a_mc_groups": part_a(),
        "part_b_chain_prng": part_b(),
    }
    out_dir = "/kaggle/working" if os.path.isdir("/kaggle") else os.getcwd()
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "out.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    # 控制台摘要(Kaggle 日志可见, 无任何敏感信息)
    print("=== mc-convergence summary ===")
    for g in out["part_a_mc_groups"]:
        p, pl = g["params"], g["pool_len"]
        print(f"[A] {g['name']}: rho={p['rho']} K_max={p['K_max']} "
              f"pool(mean={pl['mean']},p99={pl['p99']},max={pl['max']},final={pl['final_mean']}) "
              f"stop_rate={g['stop_rate']['mean']} regret_slope={g['regret_slope']['mean']} "
              f"verdict={g['verdict']}")
    b = out["part_b_chain_prng"]
    print(f"[B] repro_identical={b['schedule_repro']['identical']} "
          f"sched_hash={b['schedule_repro']['schedule_sha256'][:16]}...")
    nw = b["nw_toy"]
    print(f"[B] NW toy: design(l={nw['design']['l']},a_target={nw['design']['a_target']},"
          f"a_achieved={nw['design']['a_achieved']},m={nw['design']['m']}) "
          f"8bit->{nw['pr_output_hex']} balance={nw['balance_mean_pm1']}")
    print(f"[B] autocorr lags1-16: {json.dumps(nw['autocorr_lag1_16'])}")
    print(f"[C] out.json -> {out_path}")


if __name__ == "__main__":
    main()
