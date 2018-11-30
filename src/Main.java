import java.util.*;
import java.io.*;



/**
 * {@code Tokenizer} utility class with methods to tokenize an input stream and
 * to perform various checks on tokens.
 */
public final class Main {

    /*
     * Private members --------------------------------------------------------
     */

    /**
     * Definition of whitespace separators.
     */
    private static final String SEPARATORS = " \t\n\r,.{}();:*&|-+=[]!";


    /**
     * Returns the first "word" (maximal length string of characters not in
     * {@code SEPARATORS}) or "separator string" (maximal length string of
     * characters in {@code SEPARATORS}) in the given {@code text} starting at
     * the given {@code position}.
     *
     * @param text
     *            the {@code String} from which to get the word or separator
     *            string
     * @param position
     *            the starting index
     * @return the first word or separator string found in {@code text} starting
     *         at index {@code position}
     * @requires 0 <= position < |text|
     * @ensures <pre>
     * nextWordOrSeparator =
     *   text[position, position + |nextWordOrSeparator|)  and
     * if entries(text[position, position + 1)) intersection entries(SEPARATORS) = {}
     * then
     *   entries(nextWordOrSeparator) intersection entries(SEPARATORS) = {}  and
     *   (position + |nextWordOrSeparator| = |text|  or
     *    entries(text[position, position + |nextWordOrSeparator| + 1))
     *      intersection entries(SEPARATORS) /= {})
     * else
     *   entries(nextWordOrSeparator) is subset of entries(SEPARATORS)  and
     *   (position + |nextWordOrSeparator| = |text|  or
     *    entries(text[position, position + |nextWordOrSeparator| + 1))
     *      is not subset of entries(SEPARATORS))
     * </pre>
     */
    private static String nextWordOrSeparator(String text, int position) {
        assert text != null : "Violation of: text is not null";

        assert 0 <= position : "Violation of: 0 <= position";
        assert position < text.length() : "Violation of: position < |text|";

        String nextWordOrSeparator = "";
        StringBuilder temp = new StringBuilder();
        int pos = position;

        if (!SEPARATORS.contains(Character.toString(text.charAt(pos)))) {
            temp.append(text.charAt(pos));
            pos++;
            while (pos < text.length() && !SEPARATORS
                    .contains(Character.toString(text.charAt(pos)))) {
                temp.append(text.charAt(pos));
                pos++;
            }
        } else {
            temp.append(text.charAt(position));
            pos++;
            while (pos < text.length() && SEPARATORS
                    .contains(Character.toString(text.charAt(pos)))) {
                temp.append(text.charAt(pos));
                pos++;
            }
        }
        nextWordOrSeparator = temp.toString();
        return nextWordOrSeparator;

    }

    /*
     * Public members ---------------------------------------------------------
     */

    /**
     * Token to mark the end of the input. This token cannot come from the input
     * stream because it contains whitespace.
     */
    public static final String END_OF_INPUT = "### END OF INPUT ###";

    /**
     * Tokenizes the entire input getting rid of all whitespace separators and
     * returning the non-separator tokens in a {@code Queue<String>}.
     *
     * @param in
     *            the input stream
     * @return the queue of tokens
     * @requires in.is_open
     * @ensures <pre>
     * tokens =
     *   [the non-whitespace tokens in #in.content] * <END_OF_INPUT>  and
     * in.content = <>
     * </pre>
     */

    public static Deque<String> tokens(BufferedReader in) {

        Deque<String> output = new ArrayDeque<>();

        String line = "";

        try {
            line = in.readLine();
        } catch(IOException e) {
            System.err.println("Error with the thing");
        }

        while (line != null) {

            int i = 0;
            int lineLen = line.length();
            while (i < lineLen) {
                String token = nextWordOrSeparator(line, i);
                output.addLast(token);
                i += token.length();
            }
            output.addLast("\n");

            try {
                line = in.readLine();
            } catch(IOException e) {
                System.err.println("Error with the thing");
            }

        }
        output.addLast(END_OF_INPUT);
        return output;
    }
/*
    public static Map<String, String> buildEtoPDictionary() {
        BufferedReader dictionaryFile = null;
        try {
            dictionaryFile = new BufferedReader(new FileReader("data/PolishDictionary.txt"));
        } catch(IOException e) {
            System.err.println("Error opening file");
        }

        Map<String, String> dictionary = new HashMap<>();

        String line1 = "";
        String line2 = "";

        try {
            line1 = dictionaryFile.readLine();
            line2 = dictionaryFile.readLine();
        } catch(IOException e) {
            System.err.println("Error with the thing");
        }

        while (line1 != null) {

            dictionary.put(line1, line2);

            try {
                line1 = dictionaryFile.readLine();
                line2 = dictionaryFile.readLine();
            } catch(IOException e) {
                System.err.println("Error with the thing");
            }

        }

        return dictionary;

    }
    */

    public static Map<String, String> buildEtoPDictionary() {
        BufferedReader dictionaryFile = null;
        try {
            dictionaryFile = new BufferedReader(new FileReader("data/PolishDictionary2.txt"));
        } catch(IOException e) {
            System.err.println("Error opening file");
        }

        Map<String, String> dictionary = new HashMap<>();

        String line = "";
        String word = "";
        String definition = "";
        int splitLocation = 0;

        try {
            line = dictionaryFile.readLine();

        } catch(IOException e) {
            System.err.println("Error with the thing");
        }


        while (line != null) {

            if (line.contains(",")) {
                splitLocation = line.indexOf(',');
            }
            word = line.substring(0,splitLocation);
            definition = line.substring(splitLocation + 2);

            dictionary.put(word, definition);

            try {
                line = dictionaryFile.readLine();

            } catch(IOException e) {
                System.err.println("Error with the thing");
            }

        }

        return dictionary;

    }
/*
    public static Map<String, String> buildPtoEDictionary() {
        BufferedReader dictionaryFile = null;
        try {
            dictionaryFile = new BufferedReader(new FileReader("data/PolishDictionary.txt"));
        } catch(IOException e) {
            System.err.println("Error opening file");
        }

        Map<String, String> dictionary = new HashMap<>();

        String line1 = "";
        String line2 = "";

        try {
            line1 = dictionaryFile.readLine();
            line2 = dictionaryFile.readLine();
        } catch(IOException e) {
            System.err.println("Error with the thing");
        }

        while (line1 != null) {

            dictionary.put(line2, line1);

            try {
                line1 = dictionaryFile.readLine();
                line2 = dictionaryFile.readLine();
            } catch(IOException e) {
                System.err.println("Error with the thing");
            }

        }

        return dictionary;

    }
    */

    public static Map<String, String> buildPtoEDictionary() {
        BufferedReader dictionaryFile = null;
        try {
            dictionaryFile = new BufferedReader(new FileReader("data/PolishDictionary2.txt"));
        } catch(IOException e) {
            System.err.println("Error opening file");
        }

        Map<String, String> dictionary = new HashMap<>();

        String line = "";
        String word = "";
        String definition = "";
        int splitLocation = 0;

        try {
            line = dictionaryFile.readLine();

        } catch(IOException e) {
            System.err.println("Error with the thing");
        }


        while (line != null) {

            if (line.contains(",")) {
                splitLocation = line.indexOf(',');
            }
            definition = line.substring(0,splitLocation);
            word = line.substring(splitLocation + 2);

            dictionary.put(word, definition);

            try {
                line = dictionaryFile.readLine();

            } catch(IOException e) {
                System.err.println("Error with the thing");
            }

        }

        return dictionary;

    }

    public static Deque<String> translate(Deque<String> tokens) {

        Deque<String> output = new ArrayDeque<>();

        Map<String, String> dictionary = buildEtoPDictionary();


        while (tokens.size() > 0) {
            String word = tokens.removeFirst();
            String val = dictionary.get(word);
            if (dictionary.containsKey(word)) {
                output.addLast(val);
            } else {
                output.addLast(word);
            }
        }

        return output;
    }

    public static void detokenize(Deque<String> tokens, String outFileName) {

        PrintWriter output  = null;
        try {
            output = new PrintWriter(new BufferedWriter(new FileWriter(outFileName)));

        } catch(IOException e) {
            System.err.println("Error creating file writer");
        }

        while (tokens.size() > 1) {
            String token = tokens.removeFirst();
            //if (token.equals("\n")) {
                //System.out.println("found");
                //output.println();
            //} else {
                output.print(token);
            //}
        }

        output.close();


    }

    /*
     * Main test method -------------------------------------------------------
     */

    /**
     * Main method.
     *
     * @param args
     *            the command line arguments
     */
    public static void main(String[] args) {

        Scanner in = new Scanner(System.in);

        /*
         * Get input file name
         */
        System.out.print("Enter input file name: ");
        String inFileName = in.nextLine();

        /*
         * Tokenize input with Tokenizer implementation from library.
         */
        BufferedReader inFile = null;
        try {
            inFile = new BufferedReader(new FileReader("testfiles/" + inFileName));
        } catch(IOException e) {
            System.err.println("Error opening file");
        }

        Deque<String> tokenDeque = tokens(inFile);

        Deque<String> translatedDeque = translate(tokenDeque);


        System.out.print("Enter output file name: ");
        String outFileName = in.nextLine();
        detokenize(translatedDeque, "testfiles/" + outFileName);

        try {
            inFile.close();
        } catch(IOException e) {
            System.err.println("Error closing Buffered Reader");
        }



    }

}