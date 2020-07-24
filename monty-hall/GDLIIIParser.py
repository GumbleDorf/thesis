from problog.logic import Term, Constant,Var, Clause
from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from enum import Enum, auto
from io import StringIO
import re

class GDLFact(object):
    pass
class GDLTerm(object):
    pass

class File_Format(Enum):
    PREFIX = auto()
    POSTFIX = auto()


class GDLIIIParser(object):
    def __init__(self):
        #TODO: Grab the full list of problog builtins and populate this with them
        #If we are trying to define a predicate that is the same as a builtin, prepend a p
        self._existing_builtins = {}
        for line in open('./problog_builtins.txt'):
            self._existing_builtins[line] = f"p{line}"
        self._pred_map = {}
        self._player_count = 0

    def output_problog(self, program_file: str, file_format: File_Format):
        problog_lines = StringIO()
        self._player_count = 0
        #For now, assume file_format is POSTFIX
        process_func = {
            File_Format.POSTFIX: lambda a: problog_lines.write(self._process_line_postfix(a)),
            File_Format.PREFIX: lambda a: problog_lines.write(self._process_line_prefix(a))
        }[file_format]

        for predefined_pred in self._populate_predefined_preds():
            problog_lines.write(predefined_pred + '\n')

        for gdl_line in open(program_file):
            if gdl_line is None:
                continue
            process_func(gdl_line)
        self._pred_map = {}
        problog_lines.seek(0)
        r = open('./translated.prob', "w+")
        r.write(problog_lines.read())
        r.close()
        return PrologFile('./translated.prob')

    def _process_line_postfix(self, gdl: str):
        if ("<=" in gdl):
            return self._handle_rule_postfix(gdl)
        elif gdl.startswith('role'):
            player = gdl.replace("role(", "").replace(").", "").strip()
            if (player == "random"):
                self._pred_map[player] = str(0)
            else:
                self._player_count += 1
                self._pred_map[player] = str(self._player_count)
            return f"role({self._pred_map[player]}).\n"
        else:
            return self._handle_fact_postfix(gdl)
    #This is going to be a long function, will optimise later (I have a lot of ideas for this that are a lot cleaner)
    def _handle_rule_postfix(self, rule):
        #Replace variables first
        rule = rule.replace('<=',':-').strip()
        var_match = re.compile(r'\?.')
        var_num = 0
        for var in var_match.findall(rule):
            rule = rule.replace(str(var), "A" + "a"*var_num)
            var_num += 1
        for i in self._pred_map.keys():
            rule = rule.replace(i, self._pred_map[i])
        for i in self._existing_builtins.keys():
            rule = rule.replace(i, self._existing_builtins[i])
        if (rule.startswith('next')):
            think_rule = 'next(thinks(R,' + rule.replace('next(', "")
        else:
            think_rule = 'thinks(R,' + rule
        think_rule = think_rule.replace('ptrue(', 'thinks(R,')
        #There are better ways of doing this, but I'll redo this whole part later
        tmp = ""
        found = False
        bracket = 0
        for c in think_rule:
            if (found and c == '('):
                bracket += 1
            elif (found and c == ')'):
                bracket -= 1
            if (found and bracket == 0):
                break
            if (not found and tmp.endswith("does")):
                tmp = "does"
                found = True
                bracket += 1
            tmp += c
        if found:
            think_rule = think_rule.replace(tmp, 'thinks(R,'+tmp+')')
        think_rule = think_rule.replace(':-', ') :- role(R),')
        return rule + '\n' + think_rule + '\n'
        

    def _handle_fact_postfix(self, fact):
        for i in self._pred_map.keys():
            return fact.replace(i, self._pred_map[i]).strip() + '\n'


    #TODO: Not implemented
    def _process_line_prefix(self, gdl: str):
        pass

    #Return a list of predefined predicates that are required for the problog to run
    def _populate_predefined_preds(self):
        return [line for line in open('./data/predicates.problog')]



#Parser testing
if __name__ == "__main__":
    p = GDLIIIParser()
    print(p.output_problog('./montyhall.gdliii', File_Format.POSTFIX))