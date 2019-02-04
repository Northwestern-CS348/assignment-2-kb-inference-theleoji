import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        # print("Asserting {!r}".format(fact_rule))

        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        # print("Asking {!r}".format(fact))
        if isinstance(fact, Fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()

            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        # print("Retracting {!r}".format(fact))
        ####################################################
        # Student code goes here

        if(isinstance(fact, Fact)):
            the_fact = self._get_fact(fact)

            if the_fact.asserted and len(the_fact.supported_by):
                # if asserted and inferred
                the_fact.asserted = False
            elif len(the_fact.supported_by):
                # if just inferred
                pass
            elif the_fact.asserted:
                # if just asserted
                self.kb_remove(the_fact)
            elif not the_fact.asserted and not len(the_fact.supported_by):
                # if not asserted and not inferred
                self.kb_remove(the_fact)

    def kb_remove(self, fact):
        the_fact = self._get_fact(fact)

        for supported_fact in the_fact.supports_facts:
            for tuple in supported_fact.supported_by:
                if(tuple[0] == the_fact):
                    supported_fact.supported_by.remove(tuple)
            if len(supported_fact.supported_by) == 0 and not supported_fact.asserted:
                self.kb_retract(supported_fact)

        for supported_rule in the_fact.supports_rules:
            for tuple in supported_rule.supported_by:
                if(tuple[0] == the_fact):
                    supported_rule.supported_by.remove(tuple)
            if len(supported_rule.supported_by) == 0 and not supported_rule.asserted:
                the_rule = self._get_rule(supported_rule)
                # check supported facts by this inferred rule.
                # if that fact is not longer supported, RETRACT IT
                for supported_fact in the_rule.supports_facts:
                    for tuple in supported_fact.supported_by:
                        if(tuple[1] == the_rule):
                            supported_fact.supported_by.remove(tuple)
                    if(len(supported_fact.supported_by) == 0):
                        self.kb_retract(supported_fact)
                self.rules.remove(the_rule)
        self.facts.remove(the_fact)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            if(len(rule.lhs) == 1):
                # the rule only has one predicate on the left, so we're inferring a fact
                new_statement = instantiate(rule.rhs, bindings)
                new_fact = Fact(new_statement, [[fact, rule]])
                # print('Inferring fact', new_fact, "\n")
                kb.kb_assert(new_fact)
                fact.supports_facts.append(kb._get_fact(new_fact))
                rule.supports_facts.append(kb._get_fact(new_fact))
            else:
                # there is more than one predicate, we're inferring a rule
                new_statement = []
                for lhsItem in rule.lhs:
                    if (lhsItem != rule.lhs[0]):
                        new_statement.append(instantiate(lhsItem, bindings))
                new_rhs = instantiate(rule.rhs, bindings)
                new_rule = Rule([new_statement, new_rhs],[[fact, rule]])
                # print('Inferring rule', new_rule, "\n")
                kb.kb_assert(new_rule)
                fact.supports_rules.append(kb._get_rule(new_rule))
                rule.supports_rules.append(kb._get_rule(new_rule))
