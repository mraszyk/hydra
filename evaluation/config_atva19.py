tools = {
    "aerial": {
        "exec": "/home/hydra/aerial/aerial.native", "fmla": ".mdl", "fmla_flag": "-fmla", "log": ".log", "log_flag": "-log", "flags": "-mtl -expr -mode global", "pre_flags": "", "script": False
    },
    "hydra": {
        "exec": "/home/hydra/hydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "flags": "", "pre_flags": "", "script": False
    },
    "monpoly": {
        "exec": "/home/hydra/monpoly/monpoly", "fmla": ".mfodl", "fmla_flag": "-formula", "log": ".mlog", "log_flag": "-log", "flags": "-sig fmlas/vmon.sig", "pre_flags": "", "script": False
    },
}

formats = ["hydra", "monpoly"]

shared_log = {
    "shared": {
        "ts_cnt": 500,
        "er": 100,
        "delta": 4,
        "aps": 16,
    },
}

exps = {
    "exp_scaling": {"typ": "gen_scaling", "shared": "shared", "range": range(1, 11), "fmlas": 10, "size": 25, "max_int": 16, "type": "0", "aps": 16, "tools": ["aerial", "monpoly", "hydra"]},
    "exp_size": {"typ": "gen_size", "shared": "shared", "range": range(2, 52, 2), "fmlas": 10, "max_int": 16, "type": "0", "aps": 16, "tools": ["aerial", "monpoly", "hydra"]},
    "exp_trace": {"typ": "gen_trace", "shared": "shared", "range": range(20, 220, 20), "fmlas": 10, "delta": 4, "size": 25, "max_int": 16, "type": "0", "aps": 16, "tools": ["aerial", "monpoly", "hydra"]},
    "exp_mtl_exp": {"typ": "gen_exp", "gen": "gen_mtl_exp", "range": range(1, 12), "fmlas": 1, "len": (1 << 16), "tools": ["aerial", "monpoly", "hydra"]}
}

exp_config = {"reps": 2, "timeout": "10", "aggr": "mean"}

plot_config_exp = {
    "exp_scaling": {"case": "Average-Case", "short": "IO", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Scaling Factor", "xrange": "[0:11]", "yrange": {"time": "[0:8]", "space": "[0:30]"}, "log": {"x": None, "y": None}, "xscale": None},
    "exp_size": {"case": "Average-Case", "short": "SZ", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Formula Size", "xrange": "[0:52]", "yrange": {"time": "[0:8]", "space": "[0:30]"}, "log": {"x": None, "y": None}, "xscale": None},
    "exp_trace": {"case": "Average-Case", "short": "TR", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Trace Length [x1000]", "xrange": "[0:220]", "yrange": {"time": "[0:8]", "space": "[0:30]"}, "log": {"x": None, "y": None}, "xscale": None},
    "exp_mtl_exp": {"case": "Worst-Case", "short": "WC", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:12]", "yrange": {"time": "[0:8]", "space": "[0:30]"}, "log": {"x": None, "y": None}, "xscale": None},
}

plot_config_misc = {
    "font": "Times-Roman",
    "fontsize": "30",
    "keys": False,
}

plot_config_tools = {
    "aerial": {"name": "AERIAL", "pointtype": 4, "color": "\"0x0000FF\""},
    "hydra": {"name": "HYDRA", "pointtype": 6, "color": "\"0xFF0000\""},
    "monpoly": {"name": "MONPOLY", "pointtype": 8, "color": "\"0x000000\""}
}

plot_config_types = {
    "time": {"name": "Time Complexity", "ylabel": "Time [s]", "short": False},
    "space": {"name": "Space Complexity", "ylabel": "Space [MB]", "short": False}
}
