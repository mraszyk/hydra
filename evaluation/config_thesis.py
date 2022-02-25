tools = {
    "aerial": {
        "exec": "/home/hydra/aerial/aerial.native", "fmla": ".mdlaerial", "fmla_flag": "-fmla", "log": ".log", "log_flag": "-log", "pre_flags": "", "flags": "-mdl -expr -mode global", "script": False
    },
    "aerial_mtl": {
        "exec": "/home/hydra/aerial/aerial.native", "fmla": ".mdlaerial", "fmla_flag": "-fmla", "log": ".log", "log_flag": "-log", "pre_flags": "", "flags": "-mtl -expr -mode global", "script": False
    },
    "monpoly": {
        "exec": "/home/hydra/monpoly/monpoly", "fmla": ".mfodl", "fmla_flag": "-formula", "log": ".log", "log_flag": "-log", "flags": "-sig fmlas/vmon.sig", "pre_flags": "", "script": False
    },
    "verimon": {
        "exec": "/home/hydra/monpoly/monpoly", "fmla": ".mfodl", "fmla_flag": "-formula", "log": ".log", "log_flag": "-log", "flags": "-sig fmlas/vmon.sig -verified", "pre_flags": "", "script": False
    },
    "reelay": {
        "exec": "/home/hydra/evaluation/reelay.sh", "fmla": ".yaml", "log": ".csv", "pre_flags": "", "flags": "", "script": True
    },
    "hydra": {
        "exec": "/home/hydra/hydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "pre_flags": "", "flags": "", "script": False
    },
    "vydra": {
        "exec": "/home/hydra/vydra", "fmla": ".mdl", "fmla_flag": "", "log": ".log", "log_flag": "", "pre_flags": "", "flags": "", "script": False
    },
}

formats = ["hydra", "reelay"]

exps = {
    "exp_scaling_pmtl": {"typ": "gen_scaling", "range": range(2, 21, 2), "fmlas": 5, "size": 25, "max_int": 1000, "type": "40", "aps": 16, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon", "reelay"],
    "log": {
        "len": 100000,
        "er": 1,
        "delta": 1,
        "aps": 16,
    }},
    "exp_scaling_mtl": {"typ": "gen_scaling", "range": range(2, 21, 2), "fmlas": 5, "size": 25, "max_int": 1000, "type": "0", "aps": 16, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon"],
    "log": {
        "len": 2000,
        "er": 2,
        "delta": 100,
        "aps": 16,
    }},
    "exp_scaling_mdl": {"typ": "gen_scaling", "range": range(2, 21, 2), "fmlas": 5, "size": 25, "max_int": 100, "type": "1", "aps": 16, "tools": ["hydra", "vydra", "aerial", "verimon"],
    "log": {
        "len": 2000,
        "er": 2,
        "delta": 100,
        "aps": 16,
    }},
    "exp_mtl_fixed": {"typ": "gen_exp", "gen": "gen_mtl_fixed 1", "range": range(1000, 11000, 1000), "fmlas": 1, "len": 100000, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon", "reelay"]},
    "exp_size_pmtl": {"typ": "gen_size", "range": range(6, 52, 11), "fmlas": 5, "max_int": 50, "type": "40", "aps": 16, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon", "reelay"],
    "log": {
        "len": 100000,
        "er": 1,
        "delta": 1,
        "aps": 16,
    }},
    "exp_size_mtl": {"typ": "gen_size", "range": range(6, 52, 11), "fmlas": 5, "max_int": 50, "type": "0", "aps": 16, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon"],
    "log": {
        "len": 100000,
        "er": 10,
        "delta": 4,
        "aps": 16,
    }},
    "exp_size_mdl": {"typ": "gen_size", "range": range(6, 52, 11), "fmlas": 5, "max_int": 50, "type": "1", "aps": 16, "tools": ["hydra", "vydra", "aerial", "verimon"],
    "log": {
        "len": 1000,
        "er": 10,
        "delta": 4,
        "aps": 16,
    }},
    "exp_mtl_exp": {"typ": "gen_exp", "gen": "gen_mtl_exp", "range": range(1, 12), "fmlas": 1, "len": 10000, "tools": ["hydra", "vydra", "aerial_mtl", "monpoly", "verimon"]},
    "exp_mdl_bw_quad": {"typ": "gen_exp", "gen": "gen_mdl_quad bw", "range": range(4, 42, 4), "fmlas": 1, "len": 10000, "tools": ["hydra", "vydra", "aerial", "verimon"]},
    "exp_mdl_fw_quad": {"typ": "gen_exp", "gen": "gen_mdl_quad fw", "range": range(4, 42, 4), "fmlas": 1, "len": 10000, "tools": ["hydra", "vydra", "aerial", "verimon"]},
}

exp_config = {"reps": 1, "timeout": "200", "aggr": "median"}

plot_config_exp = {
    "exp_scaling_pmtl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Scaling Factor (n)", "xrange": "[0:22]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_scaling_mtl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Scaling Factor (n)", "xrange": "[0:22]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_scaling_mdl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Scaling Factor (n)", "xrange": "[0:22]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
     "exp_mtl_fixed": {"case": "Worst-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n x 1000)", "xrange": "[0:11]", "yrange": {"time": "[0.001:180]", "space": "[0:100]"}, "log": {"x": None, "y": 10}, "xscale": 1000},
    "exp_size_pmtl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Formula Size", "xrange": "[0:52]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_size_mtl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Formula Size", "xrange": "[0:52]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_size_mdl": {"case": "Average-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Formula Size", "xrange": "[0:52]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_mtl_exp": {"case": "Worst-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:12]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_mdl_bw_quad": {"case": "Worst-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:42]", "yrange": {"time": "[0.001:100]", "space": "[0:100]"}, "log": {"x": None, "y": "10"}, "xscale": None},
    "exp_mdl_fw_quad": {"case": "Worst-Case", "short": "", "title": True, "graph_type": "points", "size": "5,3", "xlabel": "Parameter (n)", "xrange": "[0:42]", "yrange": {"time": "[0.001:180]", "space": "[0:200]"}, "log": {"x": None, "y": "10"}, "xscale": None},
}

plot_config_misc = {
    "font": "Times-Roman",
    "fontsize": "30",
    "keys": False,
}

plot_config_tools = {
    "aerial": {"name": "AERIAL", "pointtype": 6, "color": "\"0x00AA00\""},
    "aerial_mtl": {"name": "AERIAL", "pointtype": 6, "color": "\"0x00AA00\""},
    "monpoly": {"name": "MONPOLY", "pointtype": 6, "color": "\"0x0000FF\""},
    "verimon": {"name": "VERIMON", "pointtype": 4, "color": "\"0x0000FF\""},
    "reelay": {"name": "REELAY", "pointtype": 6, "color": "\"0xAA00AA\""},
    "hydra": {"name": "HYDRA", "pointtype": 6, "color": "\"0xFF0000\""},
    "vydra": {"name": "VYDRA", "pointtype": 4, "color": "\"0x000000\""},
}

plot_config_types = {
    "time": {"name": "Time Complexity", "ylabel": "Time [s]", "short": False},
    "space": {"name": "Space Complexity", "ylabel": "Space [MB]", "short": False}
}
