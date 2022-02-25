import math
import os
import re
import sys

exec(open(sys.argv[1], "r").read())

def gen_gnuplot(exp_name, exp_type):
    f = open("tmp_" + exp_name + "_" + exp_type + ".gnuplot", "w")
    print("set terminal postscript eps enhanced color size " + plot_config_exp[exp_name]["size"] + " font '" + plot_config_misc["font"] + "," + plot_config_misc["fontsize"] + "'", file=f)
    print("set bmargin 3.5", file=f)
    print("set tmargin 2.0", file=f)
    print("set lmargin 8.5", file=f)
    print("set rmargin 4.0", file=f)
    out = exp_name + "_" + exp_type + ".eps"
    print("set output \"figs/" + out + "\"", file=f)
    if plot_config_misc["keys"] == False:
        print("unset key", file=f)
    if plot_config_exp[exp_name]["title"]:
        print("set title " + "\"" + plot_config_exp[exp_name]["case"] + " " + plot_config_types[exp_type]["name"]  + "\"", file=f)
    print("set ylabel \"" + plot_config_types[exp_type]["ylabel"] + "\" offset 2,0,0", file=f)
    print("set yrange " + plot_config_exp[exp_name]["yrange"][exp_type], file=f)
    if not plot_config_exp[exp_name]["log"]["y"] is None:
        print("set logscale y "+str(plot_config_exp[exp_name]["log"]["y"]), file=f)
    if plot_config_types[exp_type]["short"]:
       print("set label\"" + plot_config_exp[exp_name]["short"] + "\" at graph 1.03,0.5 left", file=f)
    if plot_config_exp[exp_name]["graph_type"] == "points":
        print("set xlabel \"" + plot_config_exp[exp_name]["xlabel"] + "\"", file=f)
        print("set xrange " + plot_config_exp[exp_name]["xrange"], file=f)
        if not plot_config_exp[exp_name]["log"]["x"] is None:
            print("set logscale x "+str(plot_config_exp[exp_name]["log"]["x"]), file=f)
        sep="plot "
        for tool_name in reversed(exps[exp_name]["tools"]):
            tool_dict = plot_config_tools[tool_name]
            f.write(sep)
            sep=", \\\n     "
            print("'tmp_" + tool_name + "_" + exp_type + "_S.dat' using 1:2 notitle with points pt " + str(tool_dict["pointtype"]) + " ps 1.00 lc rgbcolor " + tool_dict["color"] + ", \\", file=f)
            f.write("     'tmp_" + tool_name + "_" + exp_type + "_A.dat' using 1:2 title '" + tool_dict["name"]  + "' with linespoints pt " + str(tool_dict["pointtype"] + 1) + " ps 1.50 lw 3.00 lc rgbcolor " + tool_dict["color"])
        print("", file=f)
    elif plot_config_exp[exp_name]["graph_type"] == "bars":
        print("set boxwidth 0.45", file=f)
        print("set style fill solid", file=f)
        tool_cnt = len(exps[exp_name]["tools"])
        x=(tool_cnt - 1) * 0.25
        f.write("set xtics (")
        sep=""
        for name in exps[exp_name]["names"]:
            f.write(sep)
            sep=", "
            f.write("'" + name + "' " + str(x))
            x+=(tool_cnt - 1) * 0.5 + 1
        print(")", file=f)
        sep="plot "
        i=0
        for tool_name in exps[exp_name]["tools"]:
            tool_dict = plot_config_tools[tool_name]
            f.write(sep)
            sep=", \\\n     "
            f.write("'tmp_" + tool_name + "_" + exp_type + "_S.dat' using ($1 * " + str((tool_cnt - 1) * 0.5 + 1) + " + " + str(i * 0.5) + "):2 title '" + tool_dict["name"] + "' with boxes lc rgbcolor " + tool_dict["color"])
            i+=1
        print("", file=f)

def mean(v):
    if v == []:
        return 0.0
    return sum(v) / len(v)

def median(v):
    if v == []:
        return 0.0
    if len(v) % 2 == 0:
        return (sorted(v)[len(v) // 2 - 1] + sorted(v)[len(v) // 2]) / 2
    else:
        return sorted(v)[len(v) // 2]

def process():
    stats_time = {}
    stats_space = {}
    for exp_name, exp_dict in exps.items():
        stats_time[exp_name] = {}
        stats_space[exp_name] = {}
        for tool_name in exp_dict["tools"]:
            stats_time[exp_name][tool_name] = {}
            stats_space[exp_name][tool_name] = {}
            fts = open("tmp_" + tool_name + "_time_S.dat", "w")
            fta = open("tmp_" + tool_name + "_time_A.dat", "w")
            fss = open("tmp_" + tool_name + "_space_S.dat", "w")
            fsa = open("tmp_" + tool_name + "_space_A.dat", "w")
            for n in exp_dict["range"]:
                sn = str(n)
                if plot_config_exp[exp_name]["xscale"] is not None:
                  sn = str(n // plot_config_exp[exp_name]["xscale"])
                stats_time[exp_name][tool_name][n] = {}
                stats_space[exp_name][tool_name][n] = {}
                ta = []
                sa = []
                for f in range(exp_dict["fmlas"]):
                    stats_time[exp_name][tool_name][n][f] = []
                    stats_space[exp_name][tool_name][n][f] = []
                    for rep in range(exp_config["reps"]):
                        name = "_".join(map(str, [exp_name, n, f]))
                        tool_out_stat = "stats/stat_" + name + "_" + str(rep) + "." + tool_name
                        x = open(tool_out_stat, "r").read()
                        m = re.search("([0-9.]*) ([0-9.]*)", x)
                        stats_time[exp_name][tool_name][n][f].append(float(m.group(1)) / 1000.0)
                        if float(m.group(2)) > 0.0:
                          stats_space[exp_name][tool_name][n][f].append(float(m.group(2)) / 1000.0)
                    if exp_config["aggr"] == "mean":
                        time = mean(stats_time[exp_name][tool_name][n][f])
                        space = mean(stats_space[exp_name][tool_name][n][f])
                    elif exp_config["aggr"] == "median":
                        time = median(stats_time[exp_name][tool_name][n][f])
                        space = median(stats_space[exp_name][tool_name][n][f])
                    print(sn + " " + str(time), file=fts)
                    print(sn + " " + str(space), file=fss)
                    ta += [time]
                    sa += [space]
                if exp_config["aggr"] == "mean":
                    print(sn + " " + str(mean(ta)), file=fta)
                    print(sn + " " + str(mean(sa)), file=fsa)
                elif exp_config["aggr"] == "median":
                    print(sn + " " + str(median(ta)), file=fta)
                    print(sn + " " + str(median(sa)), file=fsa)
            fts.close()
            fta.close()
            fss.close()
            fsa.close()
        gen_gnuplot(exp_name, "time")
        os.system("gnuplot tmp_" + exp_name + "_time.gnuplot")
        gen_gnuplot(exp_name, "space")
        os.system("gnuplot tmp_" + exp_name + "_space.gnuplot")

process()
os.system("rm -f tmp_*")
