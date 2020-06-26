class World(object):
    def __init__(self, engine, kb, step, prob, preds):
        self._kb = kb
        self._engine = engine
        self._prob = prob
        self._step = step
        #List of predicates required to generate this world from the base file
        self._preds = preds

    def _addRule(self, head, body):
        b = body[0]
        for term in body[1:]:
            b = b & term
        rule = head << b
        self._preds.append(rule)
        return self._kb.add_clause(rule)

    def _addFact(self, term, probability=None):
        self._preds.append(term)
        return self._kb.add_fact(term)

    def getSuccessorWorlds(self):
        pass

    def query(self, query):
        pass

    def _relevantGround(self, queries, database):
        return self._engine.ground_all(database, queries=queries)