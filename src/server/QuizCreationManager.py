from flask import request, render_template, redirect, url_for, session, flash

"""
Description:
The QuizCreationManager class manages the process of quiz creation, including rendering forms, handling submissions, 
and storing quizzes in the database. It ensures user-defined quizzes adhere to platform restrictions, such as the 
maximum number of questions and quizzes allowed per user.

Semi-formal Notation:
/*@ requires A valid DatabaseManager instance to handle database operations &&
  @ session['email'] != null (user must be logged in);
  @ ensures Quizzes are created, validated, and stored with user restrictions enforced:
  @   - A user can create a maximum of 3 quizzes;
  @   - Each quiz can have up to 10 questions;
  @   - Quiz data is stored in the database correctly with associated user information;
@*/
"""
class QuizCreationManager:

    """
    Description:
    Initializes the QuizCreationManager instance with a DatabaseManager for executing SQL queries. This ensures 
    the manager is ready to handle quiz creation and submission tasks.

    Semi-formal Notation:
    /*@ requires db_manager != null (a valid instance of DatabaseManager);
    @ ensures self.db_manager == db_manager &&
    @ QuizCreationManager is prepared to execute database operations;
    @*/
    """
    def __init__(self, db_manager):
        self.db_manager = db_manager
        self.MAX_QUIZZES_PER_USER = 3
        self.MAX_QUESTIONS_PER_QUIZ = 10

    """
    Description:
    Handles the quiz creation process, rendering the form for quiz creation or dynamically displaying fields for 
    questions based on user input. Validates restrictions such as the maximum number of quizzes per user.

    Semi-formal Notation:
    /*@ requires request.method == 'POST' ? (request.form contains 'num_questions' && 'title') : True &&
    @ session['email'] != null;
    @ ensures If POST:
    @   - Flash error message and redirect if user has >= 3 quizzes;
    @   - Render a quiz creation form with dynamic fields for up to 10 questions;
    @ ensures If GET:
    @   - Render the initial quiz creation form (create-quiz.html);
    @*/
    """
    def create_quiz(self):
        if request.method == 'POST':
            user_email = session['email']
            if self.has_reached_quiz_limit(user_email):
                flash(f"You have reached the maximum number of quizzes allowed ({self.MAX_QUIZZES_PER_USER}).", "error")
                return redirect(url_for('create_quiz_route'))

            num_questions, title, audio_file = self.get_quiz_details_from_form()

            num_questions = self.limit_questions(num_questions)

            return self.render_quiz_creation_form(num_questions, title, audio_file=audio_file)

        return render_template('create-quiz.html')

    """
    Description:
    Handles the submission of a user-created quiz. Extracts data from the request, builds the necessary SQL query, 
    and stores the quiz in the database.

    Semi-formal Notation:
    /*@ requires request.method == 'POST' &&
    @ request.form contains 'title' &&
    @ request.form contains dynamically generated questions and options;
    @ ensures Quiz data is inserted into the database with:
    @   - User email associated with the quiz;
    @   - Up to 10 valid questions with their options and correct answers;
    @*/
    """
    def submit_quiz(self):
        if request.method == 'POST':
            title = request.form.get('title')
            user_email = session['email']
            audio_file = request.form.get('audio_file', 'option1.mp3')  # Default audio if not provided

            questions = self.build_questions_from_form()
            columns, values, placeholders = self.build_insert_query(questions, user_email, title, audio_file)

            self.store_quiz_in_database(columns, values, placeholders)
            return redirect(url_for('home'))

    """
    Description:
    Checks whether the user has reached the maximum number of quizzes allowed (3). Executes a query to count the 
    quizzes associated with the user’s email.

    Semi-formal Notation:
    /*@ requires user_email != null &&
    @ user_email is a valid string &&
    @ db_manager.execute_query(query, (user_email,)) returns a single-row result;
    @ ensures \result == (COUNT(quizzes WHERE user_email == session['email']) >= 3);
    @*/
    """
    def has_reached_quiz_limit(self, user_email):
        query = "SELECT COUNT(*) FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        return result[0][0] >= self.MAX_QUIZZES_PER_USER

    """
    Description:
    Extracts the quiz title, number of questions, and optional audio file from the submitted form. Processes and 
    validates the audio file format.

    Semi-formal Notation:
    /*@ requires request.form contains 'title', 'num_questions', and optionally 'audio_file' &&
    @ ensures \result == (request.form['num_questions'], request.form['title'], formatted_audio_file);
    @*/
    """
    def get_quiz_details_from_form(self):
        num_questions = request.form.get('num_questions')
        title = request.form.get('title')
        audio_file = request.form.get('audio_file', 'option1.mp3')

        audio_file = audio_file.replace('media/', '')

        return num_questions, title, audio_file

    """
    Description:
    Limits the number of questions to a maximum of 10. Ensures the input is a valid integer before applying the limit.

    Semi-formal Notation:
    /*@ requires num_questions is a valid integer;
    @ ensures \result == min(num_questions, 10);
    @*/
    """
    def limit_questions(self, num_questions):
        num_questions = int(num_questions)
        return min(num_questions, self.MAX_QUESTIONS_PER_QUIZ)

    """
    Description:
    Renders the quiz creation form with the specified number of questions and title. Dynamically generates fields 
    based on the number of questions requested by the user.

    Semi-formal Notation:
    /*@ requires num_questions is an integer &&
    @ title is a valid non-empty string;
    @ ensures Renders create-quiz.html with dynamically generated fields:
    @   - num_questions question fields;
    @   - Audio file field set to audio_file;
    @*/
    """
    def render_quiz_creation_form(self, num_questions, title, audio_file):
        return render_template('create-quiz.html', num_questions=num_questions, title=title, audio_file=audio_file)

    """
    Description:
    Builds a list of questions from the submitted form. Each question includes text, four options, and the correct 
    answer. Skips invalid or incomplete questions.

    Semi-formal Notation:
    /*@ requires request.form contains dynamically generated question fields:
    @   \forall i \in [0, num_questions-1] (request.form contains:
    @     f'question_text_{i}', f'answer_{i}_1', f'answer_{i}_2', f'answer_{i}_3', f'answer_{i}_4', f'correct_answer_{i}');
    @ ensures \result == [(q_text, opt1, opt2, opt3, opt4, correct) for valid questions];
    @*/
    """
    def build_questions_from_form(self):
        questions = []
        num_questions = int(request.form.get('num_questions', 0))

        for i in range(num_questions):
            # Fetch question-related fields
            question_text = request.form.get(f'question_text_{i}')
            option1 = request.form.get(f'answer_{i}_1')
            option2 = request.form.get(f'answer_{i}_2')
            option3 = request.form.get(f'answer_{i}_3')
            option4 = request.form.get(f'answer_{i}_4')
            correct_answer = request.form.get(f'correct_answer_{i}')

            # Validate the presence of a valid question text
            if not question_text or not option1 or not option2 or not option3 or not option4 or not correct_answer:
                continue  # Skip invalid or incomplete questions

            # Append only valid questions to the list
            questions.append((question_text, option1, option2, option3, option4, correct_answer))

        return questions



    """
    Description:
    Constructs the SQL query for inserting the quiz and its questions into the database. Dynamically generates 
    columns, values, and placeholders for up to 10 questions.

    Semi-formal Notation:
    /*@ requires \forall question \in questions:
    @   len(question) == 6 &&
    @   question[0] is non-empty string (question text) &&
    @   question[1..4] are non-empty strings (options) &&
    @   question[5] is one of the options (correct answer);
    @ ensures columns == ['user_email', 'title', 'audio_file', ...dynamic question columns...] &&
    @ ensures placeholders == '%s, %s, %s, ...' &&
    @ ensures values == [user_email, title, audio_file, ...flattened question values...];
    @*/
    """
    def build_insert_query(self, questions, user_email, title, audio_file):
        columns = ['user_email', 'title', 'audio_file']
        values = [user_email, title, audio_file]
        query_values_placeholders = '%s, %s, %s'

        for i, question in enumerate(questions):
            question_idx = i + 1
            columns += [
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2',
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ]
            query_values_placeholders += ', %s, %s, %s, %s, %s, %s'
            values.extend(question)

        return columns, values, query_values_placeholders


    """
    Description:
    Executes an SQL query to insert the quiz and its associated data into the `quizzes` table. Commits the transaction 
    to save the data permanently.

    Semi-formal Notation:
    /*@ requires columns is a non-empty list of valid SQL column names &&
    @ values is a list of corresponding data for the columns &&
    @ placeholders is a correctly formatted string matching len(columns);
    @ ensures Quiz is inserted into the `quizzes` table with all fields populated;
    @*/
    """
    def store_quiz_in_database(self, columns, values, placeholders):
        insert_quiz_query = f"INSERT INTO quizzes ({', '.join(columns)}) VALUES ({placeholders})"
        self.db_manager.execute_commit(insert_quiz_query, tuple(values))