from flask import request, render_template, redirect, url_for, session, flash

class QuizCreationManager:
    """
    Initialize the QuizCreationManager with a database manager
    db_manager: DatabaseManager - The manager responsible for database operations
    @requires A valid DatabaseManager instance
    @ensures QuizCreationManager is ready to handle quiz creation and submission
    """
    def __init__(self, db_manager):
        self.db_manager = db_manager

    """
    Handle the quiz creation process and render the form for quiz creation
    @requires A POST request with valid form data (title, num_questions) or a GET request to render the form
    @ensures Quiz creation form is rendered or a new quiz form is displayed with dynamic fields
    """
    def create_quiz(self):
        if request.method == 'POST':
            user_email = session['email']
            if self.has_reached_quiz_limit(user_email):
                flash("You have reached the maximum number of quizzes allowed (3).", "error")
                return redirect(url_for('create_quiz_route'))

            num_questions, title = self.get_quiz_details_from_form()
            if not num_questions or not title:
                flash("Please provide both the number of questions and the quiz title.", "error")
                return redirect(url_for('create_quiz_route'))

            num_questions = self.limit_questions(num_questions)
            return self.render_quiz_creation_form(num_questions, title)

        return render_template('create-quiz.html')

    """
    Handle the submission of the created quiz and store it in the database
    @requires A POST request with the filled quiz form data
    @ensures The quiz data is inserted into the database
    """
    def submit_quiz(self):
        if request.method == 'POST':
            title = request.form.get('title')
            user_email = session['email']
            questions = self.build_questions_from_form()
            columns, values, placeholders = self.build_insert_query(questions, user_email, title)
            self.store_quiz_in_database(columns, values, placeholders)
            return redirect(url_for('home'))

    """
    Check if the user has reached the maximum number of quizzes allowed
    user_email: str - The email of the user creating the quiz
    @requires A valid user_email and database connection
    @ensures Returns True if the user has reached the limit of 3 quizzes, else False
    """
    def has_reached_quiz_limit(self, user_email):
        query = "SELECT COUNT(*) FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        return result[0][0] >= 3

    """
    Get the quiz details (number of questions and title) from the form
    @requires The request form to contain 'num_questions' and 'title' fields
    @ensures Returns the number of questions and quiz title from the form
    """
    def get_quiz_details_from_form(self):
        num_questions = request.form.get('num_questions')
        title = request.form.get('title')
        return num_questions, title

    """
    Limit the number of questions to a maximum of 10
    num_questions: int - The number of questions input by the user
    @requires num_questions to be a valid integer
    @ensures Returns the limited number of questions, capped at 10
    """
    def limit_questions(self, num_questions):
        num_questions = int(num_questions)
        return min(num_questions, 10)

    """
    Render the form for quiz creation with the specified number of questions and title
    num_questions: int - The number of questions to create
    title: str - The title of the quiz
    @requires num_questions to be an integer and title to be a valid string
    @ensures Renders the form for creating the quiz with dynamically generated question fields
    """
    def render_quiz_creation_form(self, num_questions, title):
        return render_template('create-quiz.html', num_questions=num_questions, title=title)

    """
    Build the questions list from the form data
    @requires The request form to contain the dynamically generated questions and options
    @ensures Returns a list of questions with their respective options and correct answers
    """
    def build_questions_from_form(self):
        questions = []
        num_questions = 10  # Assuming max 10 questions
        for i in range(num_questions):
            question_text = request.form.get(f'question_text_{i}', None)
            if question_text:
                option1 = request.form.get(f'answer_{i}_1')
                option2 = request.form.get(f'answer_{i}_2')
                option3 = request.form.get(f'answer_{i}_3')
                option4 = request.form.get(f'answer_{i}_4')
                correct_answer = request.form.get(f'correct_answer_{i}')
                questions.append((question_text, option1, option2, option3, option4, correct_answer))
        return questions

    """
    Build the SQL query to insert the quiz into the database
    questions: list - The list of questions with their options and correct answers
    user_email: str - The email of the user creating the quiz
    title: str - The title of the quiz
    @requires A valid list of questions, user_email, and title
    @ensures Returns the columns, values, and query placeholders for the SQL insert statement
    """
    def build_insert_query(self, questions, user_email, title):
        columns = ['user_email', 'title']
        values = [user_email, title]
        query_values_placeholders = '%s, %s'

        for i in range(len(questions)):
            question_idx = i + 1
            columns += [
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2',
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ]
            query_values_placeholders += ', %s, %s, %s, %s, %s, %s'
            values.extend(questions[i])

        return columns, values, query_values_placeholders

    """
    Store the created quiz in the database
    columns: list - The list of column names for the SQL insert statement
    values: list - The values to be inserted into the columns
    placeholders: str - The placeholders for the SQL insert query
    @requires Valid columns, values, and placeholders
    @ensures The quiz is inserted into the quizzes table in the database
    """
    def store_quiz_in_database(self, columns, values, placeholders):
        insert_quiz_query = f"INSERT INTO quizzes ({', '.join(columns)}) VALUES ({placeholders})"
        self.db_manager.execute_commit(insert_quiz_query, tuple(values))
