import re
import sys

exec(open(sys.argv[1], "r").read())

bash = open("./run.sh", "w")

def gen_fmla(prefix, param, seed, size, max_int, typ, scale, aps):
    name = "_".join(map(str, [prefix, param, seed]))
    print("./gen_fmla fmlas/" + " ".join(map(str, [name, size, max_int, typ, scale, seed, aps])), file=bash)

def gen_log(prefix, ts_cnt, er, delta, seed, aps):
    print("./gen_log logs/" + " ".join(map(str, [prefix, ts_cnt, er, delta, seed, aps])), file=bash)

def gen_log_symlink(path, prefix, param, seed):
    name = "_".join(map(str, [prefix, param, seed]))
    for tool_name in formats:
        tool_dict = tools[tool_name]
        print("ln -fs " + path + tool_dict["log"] + " logs/" + name + tool_dict["log"], file=bash)

def run_experiment(prefix, tool_list, param, seed):
    for rep in range(exp_config["reps"]):
        for tool_name in tool_list:
            tool_dict = tools[tool_name]
            name = "_".join(map(str, [prefix, param, seed]))
            fmla = "fmlas/" + name + tool_dict["fmla"]
            if "sig" in tool_dict:
                sig = "fmlas/" + name + tool_dict["sig"]
            log = "logs/" + name + tool_dict["log"]
            tool_out_stat = "stats/stat_" + name + "_" + str(rep) + "." + tool_name
            if tool_dict["script"]:
                tool_exec_line = tool_dict["exec"] + " ".join(map(str, ["", exp_config["timeout"], tool_dict["pre_flags"], fmla, log, tool_dict["flags"]]))
                print(tool_exec_line + ' > ' + tool_out_stat, file=bash)
            else:
                if "sig" in tool_dict:
                    tool_exec_line = tool_dict["exec"] + " ".join(map(str, ["", tool_dict["pre_flags"], tool_dict["fmla_flag"], fmla, tool_dict["log_flag"], log, tool_dict["sig_flag"], sig, tool_dict["flags"]]))
                else:
                    tool_exec_line = tool_dict["exec"] + " ".join(map(str, ["", tool_dict["pre_flags"], tool_dict["fmla_flag"], fmla, tool_dict["log_flag"], log, tool_dict["flags"]]))
                print('./run ' + exp_config["timeout"] + ' ' + tool_exec_line + ' > ' + tool_out_stat, file=bash)

def gen_scaling(name):
    for n in exps[name]["range"]:
        for f in range(exps[name]["fmlas"]):
            gen_fmla(name, n, f, exps[name]["size"], exps[name]["max_int"], exps[name]["type"], n, exps[name]["aps"])
            gen_log_symlink(exps[name]["shared"], name, n, f)
            run_experiment(name, exps[name]["tools"], n, f)

def gen_size(name):
    for size in exps[name]["range"]:
        for f in range(exps[name]["fmlas"]):
            gen_fmla(name, size, f, size, exps[name]["max_int"], exps[name]["type"], 1, exps[name]["aps"])
            gen_log_symlink(exps[name]["shared"], name, size, f)
            run_experiment(name, exps[name]["tools"], size, f)

def gen_trace(name):
    for er in exps[name]["range"]:
        log_name = "_".join(map(str, [name, er]))
        gen_log(log_name, 100, 10 * er, exps[name]["delta"], 0, exps[name]["aps"])
        for f in range(exps[name]["fmlas"]):
            gen_fmla(name, er, f, exps[name]["size"], exps[name]["max_int"], exps[name]["type"], 1, exps[name]["aps"])
            gen_log_symlink(log_name, name, er, f)
            run_experiment(name, exps[name]["tools"], er, f)

def gen_exp(name):
    for i in exps[name]["range"]:
        file_name = "_".join(map(str, [name, i, 0]))
        print("./" + exps[name]["gen"] + " ".join(map(str, ["", "fmlas/" + file_name, "logs/" + file_name, i, exps[name]["len"]])), file=bash)
        run_experiment(name, exps[name]["tools"], i, 0)

def gen_fixed(name):
    for i in range(len(exps[name]["names"])):
        run_experiment(name, exps[name]["tools"], i, 0)

def main():
    for log_name, log_dict in shared_log.items():
        gen_log(log_name, log_dict["ts_cnt"], log_dict["er"], log_dict["delta"], 0, log_dict["aps"])
    for exp_name, exp_dict in exps.items():
        if exp_dict["typ"] == "gen_scaling":
            gen_scaling(exp_name)
        elif exp_dict["typ"] == "gen_size":
            gen_size(exp_name)
        elif exp_dict["typ"] == "gen_trace":
            gen_trace(exp_name)
        elif exp_dict["typ"] == "gen_exp":
            gen_exp(exp_name)
        else:
            assert(0)

main()
bash.close()
