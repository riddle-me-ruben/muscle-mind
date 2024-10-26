from flask import request, redirect, url_for, render_template, session, flash

class QuizManager:
    def __init__(self, db_manager, session):
        self.db_manager = db_manager
        self.session = session

    # Function to fetch quizzes for the logged-in user
    def get_quiz_by_id(self, quiz_id):
        # Query to get the quiz details
        quiz_query = "SELECT title FROM quizzes WHERE quiz_id = %s"
        quiz = self.db_manager.execute_query(quiz_query, (quiz_id,))

        if not quiz:
            return None  # Return None if the quiz is not found

        # Query to get the quiz questions
        question_query = """
        SELECT question_text, option1, option2, option3, option4, correct_option
        FROM questions WHERE quiz_id = %s
        """
        questions = self.db_manager.execute_query(question_query, (quiz_id,))
        print(type(questions))
        return {'quiz': quiz[0], 'questions': questions}

    # Method to fetch quizzes for the logged-in user
    def get_user_quizzes(self, user_email):
        query = "SELECT quiz_id, title FROM quizzes WHERE user_email = %s"
        quizzes = self.db_manager.execute_query(query, (user_email,))
        return quizzes

    # Function to check if a user has reached the quiz creation limit
    def has_reached_quiz_limit(self, user_email):
        query = "SELECT COUNT(*) FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        quiz_count = result[0][0]
        return quiz_count >= 3


    # Function to render the quiz creation form based on user input for the number of questions
    def create_quiz(self):
        user_email = self.session['email']  # Assuming you have user_id stored in the session

        # Check if the user has reached the quiz creation limit
        if self.has_reached_quiz_limit(user_email):
            flash("You have reached the maximum number of quizzes allowed (3).", "error")
            return redirect(url_for('create_quiz_route'))


        num_questions = request.form.get('num_questions')  # Safely get the number of questions
        title = request.form.get('title')
        if num_questions:
            num_questions = int(num_questions)
        else:
            return redirect(url_for('home'))  # Redirect if no 'num_questions' is provided

        if num_questions > 10:  # Limit the number of questions to 10
            num_questions = 10

        # Create a list of placeholder questions based on the number provided by the user
        questions = [f"Question {i+1}" for i in range(num_questions)]
        return render_template('create-quiz.html', questions=questions, title=title, num_questions=num_questions)

    # Function to handle form submission for quiz and store everything in one table
    def submit_quiz(self):
        if request.method == 'POST':
            title = request.form.get('title')
            user_email = self.session['email']  # Assuming you have user_id stored in the session

            # Prepare to collect up to 10 questions and their options
            questions = []
            num_questions = 10  # Assuming max 10 questions, you can dynamically adjust this if needed
            for i in range(num_questions):
                question_text = request.form.get(f'question_text_{i}', None)
                if question_text:
                    option1 = request.form.get(f'answer_{i}_1')
                    option2 = request.form.get(f'answer_{i}_2')
                    option3 = request.form.get(f'answer_{i}_3')
                    option4 = request.form.get(f'answer_{i}_4')
                    correct_answer = request.form.get(f'correct_answer_{i}')
                    questions.append((question_text, option1, option2, option3, option4, correct_answer))

            # Dynamically build the insert query for questions
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

                # Add values for the current question and options
                values.extend(questions[i])

            # Build the complete query
            insert_quiz_query = f"INSERT INTO quizzes ({', '.join(columns)}) VALUES ({query_values_placeholders})"

            # Execute the query to store the quiz and questions
            self.db_manager.execute_commit(insert_quiz_query, tuple(values))

            return redirect(url_for('home'))


    def get_quiz_by_id(self, quiz_id):
        # Build the select query dynamically for all questions and their options
        columns = ['title']
        num_questions = 10  # Assuming max 10 questions, adjust if needed

        for i in range(num_questions):
            question_idx = i + 1
            columns += [
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2', 
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ]

        quiz_query = f"SELECT {', '.join(columns)} FROM quizzes WHERE quiz_id = %s"

        # Execute the query to fetch the quiz and its questions
        quiz = self.db_manager.execute_query(quiz_query, (quiz_id,))

        if not quiz:
            return None  # Return None if the quiz is not found

        # Dynamically build the questions list to return
        questions = []
        for i in range(num_questions):
            question_idx = 1 + i * 6  # question text index and options start from this point in the result
            if quiz[0][question_idx]:
                questions.append({
                    'question': quiz[0][question_idx],
                    'options': [quiz[0][question_idx + 1], quiz[0][question_idx + 2], quiz[0][question_idx + 3], quiz[0][question_idx + 4]],
                    'correct_option': quiz[0][question_idx + 5]
                })

        return {
            'title': quiz[0][0],  # The title is always the first column
            'questions': questions
        }
