tools = {
    "aerial": {
        "exec": "/home/hydra/aerial/aerial.native", "fmla": ".mdl", "fmla_flag": "-fmla", "log": ".log", "log_flag": "-log", "pre_flags": "", "flags": "-mdl -expr -mode global", "script": False
    },
    "aerial_mtl": {
        "exec": "/home/hydra/aerial/aerial.native", "fmla": ".mdl", "fmla_flag": "-fmla", "log": ".log", "log_flag": "-log", "pre_flags": "", "flags": "-mtl -expr -mode global", "script": False
    },
    "hydra": {
        "exec": "/home/hydra/hydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "pre_flags": "", "flags": "-pure_mdl", "script": False
    },
    "hydra_mtl": {
        "exec": "/home/hydra/hydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "pre_flags": "", "flags": "", "script": False
    },
    "pcre": {
        "exec": "/home/hydra/pcre2/build/pcre2grep", "fmla": ".pcre", "fmla_flag": "-f", "log": ".txt", "log_flag": "", "pre_flags": "-o --buffer-size=2500000", "flags": "", "script": False,
    },
    "reelay": {
        "exec": "/home/hydra/evaluation/reelay.sh", "fmla": ".yaml", "log": ".csv", "pre_flags": "", "flags": "", "script": True
    },
    "r2u2": {
        "exec": "/home/hydra/evaluation/r2u2.sh", "fmla": ".mltl", "log": ".r2u2", "pre_flags": "", "flags": "", "script": True
    },
    "vydra": {
        "exec": "/home/hydra/vydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "pre_flags": "", "flags": "", "script": False
    },
}

formats = ["hydra", "reelay"]

shared_log = {
    "shared": {
        "ts_cnt": 2000,
        "er": 10,
        "delta": 4,
        "aps": 16,
    },
}

exps = {
    "exp_scaling": {"typ": "gen_scaling", "shared": "shared", "range": range(1, 11), "fmlas": 10, "size": 25, "max_int": 50, "type": "1", "aps": 16, "tools": ["aerial", "hydra", "vydra"]},
    "exp_size": {"typ": "gen_size", "shared": "shared", "range": range(2, 52, 4), "fmlas": 10, "max_int": 16, "type": "1", "aps": 16, "tools": ["aerial", "hydra", "vydra"]},
    "exp_mtl_exp": {"typ": "gen_exp", "gen": "gen_mtl_exp", "range": range(1, 12), "fmlas": 1, "len": (1 << 13), "tools": ["aerial_mtl", "hydra", "hydra_mtl", "vydra"]},
    "exp_mtl_fixed": {"typ": "gen_exp", "gen": "gen_mtl_fixed 1", "range": range(2000, 22000, 2000), "fmlas": 1, "len": 40000, "tools": ["aerial_mtl", "hydra", "hydra_mtl", "reelay", "vydra"]},
    "exp_pcre": {"typ": "gen_exp", "gen": "gen_pcre", "range": range(10, 110, 10), "fmlas": 1, "len": 100000, "tools": ["pcre", "hydra", "vydra"]},
}

exp_config = {"reps": 2, "timeout": "90", "aggr": "mean"}

plot_config_exp = {
    "exp_scaling": {"case": "Average-Case", "short": "IO", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Scaling Factor", "xrange": "[0:11]", "yrange": {"time": "[0.01:20]", "space": "[0:30]"}, "log": {"x": None, "y": 10}, "xscale": None},
    "exp_size": {"case": "Average-Case", "short": "SZ", "title": False, "graph_type": "points", "size": "5,3", "xlabel": "Formula Size", "xrange": "[0:52]", "yrange": {"time": "[0.001:20]", "space": "[0:30]"}, "log": {"x": None, "y": 10}, "xscale": None},
    "exp_mtl_exp": {"case": "Worst-Case (MTL)", "short": "WC", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:12]", "yrange": {"time": "[0.001:20]", "space": "[0:30]"}, "log": {"x": None, "y": 10}, "xscale": None},
    "exp_mtl_fixed": {"case": "Fixed Data (MTL)", "short": "RL", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:22]", "yrange": {"time": "[0.001:80]", "space": "[0:30]"}, "log": {"x": None, "y": 10}, "xscale": 1000},
    "exp_pcre": {"case": "PCRE", "short": "RE", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:110]", "yrange": {"time": "[0.01:20]", "space": "[0:30]"}, "log": {"x": None, "y": 10}, "xscale": None},
}

plot_config_misc = {
    "font": "Times-Roman",
    "fontsize": "30",
    "keys": False,
}

plot_config_tools = {
    "aerial": {"name": "AERIAL(MDL)", "pointtype": 4, "color": "\"0x0000FF\""},
    "aerial_mtl": {"name": "AERIAL(MTL)", "pointtype": 4, "color": "\"0x0000AA\""},
    "hydra": {"name": "HYDRA(MDL)", "pointtype": 6, "color": "\"0xFF0000\""},
    "hydra_mtl": {"name": "HYDRA(MTL)", "pointtype": 6, "color": "\"0xAA0000\""},
    "pcre": {"name": "PCRE2", "pointtype": 4, "color": "\"0x0000FF\""},
    "reelay": {"name": "REELAY", "pointtype": 8, "color": "\"0x00AA00\""},
    "r2u2": {"name": "R2U2", "pointtype": 8, "color": "\"0xAA00AA\""},
    "vydra": {"name": "VYDRA(MDL)", "pointtype": 6, "color": "\"0x000000\""},
}

plot_config_types = {
    "time": {"name": "Time Complexity", "ylabel": "Time [s]", "short": False},
    "space": {"name": "Space Complexity", "ylabel": "Space [MB]", "short": True}
}
