public static void renameInstruction(Program prog, String oldName, String newName) {
        Statement body = this.replaceBody(this.newBody());
        renameInstruction(body, oldName, newName);
        this.replaceBody(body);

        Map<String, Statement> newContext = prog.newContext();
        Map<String, Statement> oldContext = prog.replaceContext(newContext);

        while(oldContext.size() > 0) {
        Map.Pair<String, Statement> pair = oldContext.removeAny();
        renameInstruction(pair.value(), oldName, newName);
        if(pair.key().equals(oldName)) {
        newContext.add(newName, pair.value());
        } else {
        newContext.add(pair.key(), pair.value());
        }
        }
        prog.replaceContext(newContext)l


}