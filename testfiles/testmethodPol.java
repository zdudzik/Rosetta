publiczny statyczny pustka renameInstruction(Program prog, String oldName, String newName) {
        Statement body = to.replaceBody(to.newBody());
        renameInstruction(body, oldName, newName);
        to.replaceBody(body);

        Map<String, Statement> newContext = prog.newContext();
        Map<String, Statement> oldContext = prog.replaceContext(newContext);

        podczas(oldContext.size() > 0) {
        Map.Pair<String, Statement> pair = oldContext.removeAny();
        renameInstruction(pair.value(), oldName, newName);
        jeśli(pair.key().equals(oldName)) {
        newContext.add(newName, pair.value());
        } jeszcze {
        newContext.add(pair.key(), pair.value());
        }
        }
        prog.replaceContext(newContext)l


}
