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
        # Check if it's a POST request to handle form submission
        if request.method == 'POST':
            user_email = session['email']

            # Check if the user has reached their quiz limit
            if self.has_reached_quiz_limit(user_email):
                flash("You have reached the maximum number of quizzes allowed (3).", "error")
                return redirect(url_for('create_quiz_route'))

            # Get the number of questions and quiz title from the form
            num_questions = request.form.get('num_questions')
            title = request.form.get('title')

            # Ensure num_questions is valid
            if not num_questions or not title:
                flash("Please provide both the number of questions and the quiz title.", "error")
                return redirect(url_for('create_quiz_route'))

            # Ensure num_questions is an integer
            num_questions = int(num_questions)

            # Limit the number of questions to 10
            if num_questions > 10:
                num_questions = 10

            # Render the second form with dynamically generated question fields
            return render_template('create-quiz.html', num_questions=num_questions, title=title)

        # If it's a GET request, simply render the initial form (to input title and number of questions)
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

            questions = []
            num_questions = 10
            for i in range(num_questions):
                question_text = request.form.get(f'question_text_{i}', None)
                if question_text:
                    option1 = request.form.get(f'answer_{i}_1')
                    option2 = request.form.get(f'answer_{i}_2')
                    option3 = request.form.get(f'answer_{i}_3')
                    option4 = request.form.get(f'answer_{i}_4')
                    correct_answer = request.form.get(f'correct_answer_{i}')
                    questions.append((question_text, option1, option2, option3, option4, correct_answer))

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

            insert_quiz_query = f"INSERT INTO quizzes ({', '.join(columns)}) VALUES ({query_values_placeholders})"
            self.db_manager.execute_commit(insert_quiz_query, tuple(values))

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
